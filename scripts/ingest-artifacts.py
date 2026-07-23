#!/usr/bin/env python3
"""Build the versioned JSON-LD artifact registry.

The script is deliberately dependency-free.  It extracts only facts available
in the repository: Lean declaration headers, corpus metadata, source locations,
and explicit literature references in nearby Lean documentation.  It does not
guess theorem dependencies or claim a theorem is proved merely because a paper
mentions it.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = Path("dataset/extracted/rh_corpus_database_complete.json")
DEFAULT_LEAN_ROOT = Path("proofs")
DEFAULT_ROADMAP = Path("ARTIFACT_DATABASE_ROADMAP.md")
DEFAULT_CURATION = Path("artifacts/curation.json")
DEFAULT_PAPER_ROOT = Path("artifacts/papers")
DEFAULT_OUTPUT = Path("artifacts/registry.jsonld")

CONTEXT = {
    "@vocab": "https://riemann-hypothesis.github.io/artifacts#",
    "dependsOn": {"@type": "@id"},
    "motivatedBy": {"@type": "@id"},
    "formalizes": {"@type": "@id"},
    "blockedBy": {"@type": "@id"},
}

DECL_RE = re.compile(
    r"^\s*(?:(?:protected|private|noncomputable)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|axiom)\s+([A-Za-z_][\w'.]*)\b"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.]*)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+.*)?$")
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.]*))?\s*$")
PAPER_ID_RE = re.compile(r"(?<!\d)(?:arXiv\s*:?\s*)?(\d{4}\.\d{4,5})(?:v\d+)?", re.I)
MARKDOWN_HEADING_RE = re.compile(r"^(#{1,3})\s+(.+?)\s*$")


def slug(value: str) -> str:
    """Return a stable readable identifier component without external packages."""
    normalized = value.lower().replace("mö", "moe").replace("ö", "o")
    normalized = re.sub(r"[^a-z0-9]+", "-", normalized)
    return normalized.strip("-") or "unnamed"


def repo_relative(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError:
        return path.as_posix()


def git_revision_for_path(root: Path, path: Path) -> str | None:
    """Return the commit that last changed a source input, not HEAD.

    This keeps a checked-in registry reproducible: changing the indexer itself
    does not rewrite every formal artifact's provenance.
    """
    try:
        return subprocess.check_output(
            ["git", "log", "-1", "--format=%H", "--", repo_relative(path, root)],
            cwd=root,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Mask block and line comments while retaining line numbers.

    Lean supports nested `/- ... -/` comments.  The parser below is intentionally
    modest; it only needs declaration headers and avoids treating documentation
    examples as declarations.
    """
    output: list[str] = []
    depth = 0
    for original in lines:
        line = original
        chars: list[str] = []
        index = 0
        while index < len(line):
            pair = line[index : index + 2]
            if depth and pair == "/-":
                depth += 1
                index += 2
            elif depth and pair == "-/":
                depth -= 1
                index += 2
            elif depth:
                index += 1
            elif pair == "/-":
                depth = 1
                index += 2
            elif pair == "--":
                break
            else:
                chars.append(line[index])
                index += 1
        output.append("".join(chars))
    return output


def enclosing_doc(lines: list[str], line_number: int) -> str:
    """Return the nearest preceding Lean doc block, if any."""
    index = line_number - 2
    while index >= 0 and not lines[index].strip():
        index -= 1
    if index < 0 or "-/" not in lines[index]:
        return ""
    collected: list[str] = []
    while index >= 0:
        collected.append(lines[index])
        if "/-" in lines[index]:
            break
        index -= 1
    return "\n".join(reversed(collected))


def declaration_header(code_lines: list[str], start: int, kind: str) -> tuple[str, int]:
    """Read a compact Lean declaration header and return its final line index."""
    header: list[str] = []
    for index in range(start, min(len(code_lines), start + 80)):
        line = code_lines[index].strip()
        if index > start and DECL_RE.match(line):
            break
        if not line and header:
            break
        header.append(line)
        joined = " ".join(header)
        if kind in {"structure", "class"} and re.search(r"\bwhere\b", joined):
            return joined.split("where", 1)[0].strip(), index
        if ":=" in joined:
            return joined.split(":=", 1)[0].strip(), index
        if kind == "axiom" and index > start and not line:
            break
    return " ".join(header).strip(), min(len(code_lines) - 1, start + len(header) - 1)


def declaration_type(kind: str) -> str:
    return {
        "theorem": "FormalTheorem",
        "lemma": "FormalLemma",
        "def": "FormalDefinition",
        "abbrev": "FormalDefinition",
        "axiom": "FormalAxiom",
        "structure": "FormalStructure",
        "class": "FormalStructure",
    }[kind]


def verification_status(kind: str, block: str) -> dict[str, Any]:
    if kind == "axiom":
        return {"status": "assumed", "newAxioms": 1, "sorries": 0}
    if re.search(r"\b(?:sorry|admit)\b", block):
        return {"status": "contains_sorry", "newAxioms": 0, "sorries": 1}
    if kind in {"theorem", "lemma"}:
        return {"status": "proved", "newAxioms": 0, "sorries": 0}
    return {"status": "declaration", "newAxioms": 0, "sorries": 0}


def paper_ids_in(text: str, known_ids: set[str]) -> list[str]:
    ids = {match.group(1) for match in PAPER_ID_RE.finditer(text)}
    return sorted(ids & known_ids)


def extract_lean_artifacts(
    lean_root: Path, root: Path, known_papers: set[str]
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    artifacts: list[dict[str, Any]] = []
    relationships: list[dict[str, Any]] = []
    if not lean_root.exists():
        return artifacts, relationships

    for path in sorted(lean_root.rglob("*.lean")):
        revision = git_revision_for_path(root, path)
        original = path.read_text(encoding="utf-8").splitlines()
        code = strip_lean_comments(original)
        scopes: list[tuple[str, str | None]] = []
        declarations: list[tuple[int, str, str, str, int]] = []
        module_name = path.relative_to(lean_root).with_suffix("").as_posix().replace("/", ".")
        module_id = f"module:{module_name}"
        module_source: dict[str, Any] = {"file": repo_relative(path, root), "line": 1, "module": module_name}
        if revision:
            module_source["commit"] = revision
        artifacts.append(
            {
                "@id": module_id,
                "@type": "FormalModule",
                "name": module_name,
                "source": module_source,
                "tags": ["lean", "module"],
            }
        )
        for index, line in enumerate(code):
            namespace = NAMESPACE_RE.match(line)
            if namespace:
                scopes.append(("namespace", namespace.group(1)))
                continue
            if SECTION_RE.match(line):
                scopes.append(("section", None))
                continue
            end = END_RE.match(line)
            if end:
                if scopes:
                    scopes.pop()
                continue
            declaration = DECL_RE.match(line)
            if not declaration:
                continue
            kind, local_name = declaration.groups()
            namespaces = [name for scope, name in scopes if scope == "namespace" and name]
            qualified = local_name if "." in local_name else ".".join([*namespaces, local_name])
            header, end_index = declaration_header(code, index, kind)
            declarations.append((index, kind, local_name, qualified, end_index))

        for position, (start, kind, local_name, qualified, header_end) in enumerate(declarations):
            next_start = declarations[position + 1][0] if position + 1 < len(declarations) else len(code)
            source_block = "\n".join(code[start:next_start])
            doc = enclosing_doc(original, start + 1)
            header, _ = declaration_header(code, start, kind)
            artifact_id = f"{kind}:{qualified}"
            file_name = repo_relative(path, root)
            artifact = {
                "@id": artifact_id,
                "@type": declaration_type(kind),
                "name": qualified,
                "statement": header,
                "source": {
                    "file": file_name,
                    "line": start + 1,
                    "module": path.relative_to(lean_root).with_suffix("").as_posix().replace("/", "."),
                },
                "verification": verification_status(kind, source_block),
                "tags": ["lean", path.parent.name.lower()],
            }
            status = artifact["verification"]["status"]
            if status in {"assumed", "contains_sorry"}:
                artifact["openProblem"] = True
                artifact["difficulty"] = "research-level"
                artifact["tags"].append("unresolved-formalization")
            if revision:
                artifact["source"]["commit"] = revision
            if doc:
                artifact["summary"] = re.sub(r"\s+", " ", doc).replace("/-", "").replace("-/", "").strip()
            artifacts.append(artifact)
            relationships.append(
                {
                    "source": artifact_id,
                    "predicate": "derivedFrom",
                    "target": module_id,
                    "confidence": 1.0,
                    "note": "Declaration is defined in this Lean module.",
                }
            )
            for paper_id in paper_ids_in(doc, known_papers):
                relationships.append(
                    {
                        "source": artifact_id,
                        "predicate": "motivatedBy",
                        "target": f"paper:{paper_id}",
                        "confidence": 1.0,
                        "note": "Explicit arXiv identifier in the declaration's preceding documentation.",
                    }
                )
    return artifacts, relationships


def load_corpus(corpus_path: Path) -> dict[str, Any]:
    with corpus_path.open(encoding="utf-8") as handle:
        return json.load(handle)


def load_curation(path: Path) -> dict[str, Any]:
    """Load optional, source-verified corrections and bibliography records.

    The corpus contains valuable working metadata but also legacy shorthand
    author names and collective labels.  Curation is intentionally small and
    explicit: it corrects only records with a reference we are willing to show
    on the public site, while retaining all original corpus records.
    """
    if not path.exists():
        return {}
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError("artifact curation must be a JSON object")
    for key in ("overrides", "artifacts", "relationships"):
        if key in data and not isinstance(data[key], (dict, list)):
            raise ValueError(f"artifact curation {key} has an invalid shape")
    return data


def load_paper_artifacts(paper_root: Path, root: Path) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Load source-reviewed H15 paper records and their explicit audit links.

    Each JSON file is intentionally a small, reviewable bibliographic record.
    It may add an audit finding, but never upgrades a research paper into a
    formal proof. The corresponding relationships are labelled ``informs`` so
    the public graph records relevance without claiming derivation.
    """
    if not paper_root.exists():
        return [], []

    artifacts: list[dict[str, Any]] = []
    relationships: list[dict[str, Any]] = []
    for path in sorted(paper_root.glob("*.json")):
        with path.open(encoding="utf-8") as handle:
            paper = json.load(handle)
        if not isinstance(paper, dict):
            raise ValueError(f"paper metadata is not an object: {repo_relative(path, root)}")
        paper_id = paper.get("@id")
        title = paper.get("title") or paper.get("name")
        if not isinstance(paper_id, str) or not paper_id.startswith("paper:"):
            raise ValueError(f"paper metadata needs a paper: @id: {repo_relative(path, root)}")
        if paper.get("@type") != "SourcePaper" or not isinstance(title, str) or not title.strip():
            raise ValueError(f"paper metadata needs a SourcePaper title: {repo_relative(path, root)}")
        authors = paper.get("authors", [])
        keywords = paper.get("keywords", [])
        related = paper.get("relatedArtifacts", [])
        if not isinstance(authors, list) or not all(isinstance(author, str) and author.strip() for author in authors):
            raise ValueError(f"paper metadata has invalid authors: {repo_relative(path, root)}")
        if not isinstance(keywords, list) or not all(isinstance(keyword, str) for keyword in keywords):
            raise ValueError(f"paper metadata has invalid keywords: {repo_relative(path, root)}")
        if not isinstance(related, list) or not all(isinstance(target, str) and target for target in related):
            raise ValueError(f"paper metadata has invalid relatedArtifacts: {repo_relative(path, root)}")

        artifact = dict(paper)
        artifact["name"] = title.strip()
        artifact["source"] = {"file": repo_relative(path, root), "line": 1}
        artifact["localPdf"] = paper.get("pdfLocal")
        artifact["tags"] = sorted({*paper.get("tags", []), *keywords})
        if paper.get("abstract") and not paper.get("summary"):
            artifact["summary"] = paper["abstract"]
        artifacts.append(artifact)

        for author in authors:
            author_id = f"mathematician:{slug(author)}"
            artifacts.append({"@id": author_id, "@type": "Mathematician", "name": author})
            relationships.append(
                {
                    "source": paper_id,
                    "predicate": "authoredBy",
                    "target": author_id,
                    "confidence": 1.0,
                    "note": "Author attribution recorded in the audited paper metadata.",
                }
            )
        for target in related:
            relationships.append(
                {
                    "source": paper_id,
                    "predicate": "informs",
                    "target": target,
                    "confidence": 0.8,
                    "note": "Recorded H15 research relevance; not a claim that the paper proves this artifact.",
                }
            )
    return artifacts, relationships


def extract_corpus_artifacts(corpus: dict[str, Any]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    artifacts: list[dict[str, Any]] = []
    relationships: list[dict[str, Any]] = []
    articles = corpus.get("articles", [])
    insights = {item.get("article_id"): item for item in corpus.get("insights", [])}
    formalization = {item.get("article_id"): item for item in corpus.get("formalization", [])}

    article_ids = {str(article["id"]) for article in articles if article.get("id")}
    for article in articles:
        raw_id = str(article["id"])
        paper_id = f"paper:{raw_id}"
        tags = sorted({str(tag) for tag in article.get("tags", []) if tag})
        artifact: dict[str, Any] = {
            "@id": paper_id,
            "@type": "SourcePaper",
            "name": article.get("title") or raw_id,
            "year": article.get("year"),
            "arxivId": article.get("arxiv_id"),
            "doi": article.get("doi"),
            "journal": article.get("journal"),
            "roleInProject": article.get("role_in_project"),
            "relevanceScore": article.get("relevance_score"),
            "localPdf": article.get("local_pdf_path"),
            "tags": tags,
        }
        if raw_id in insights:
            insight = insights[raw_id]
            artifact["summary"] = insight.get("main_contribution")
            artifact["openProblems"] = insight.get("open_problems", [])
        if raw_id in formalization:
            readiness = formalization[raw_id]
            artifact["formalizationPotential"] = {
                "overallReadiness": readiness.get("overall_readiness"),
                "estimatedWeeks": readiness.get("estimated_weeks"),
                "mathlibDependencies": readiness.get("mathlib_dependencies", []),
            }
        artifacts.append(artifact)

        for author in article.get("authors", []):
            name = author.get("name") if isinstance(author, dict) else str(author)
            if not name:
                continue
            author_id = f"mathematician:{slug(name)}"
            artifacts.append({"@id": author_id, "@type": "Mathematician", "name": name})
            relationships.append(
                {"source": paper_id, "predicate": "authoredBy", "target": author_id, "confidence": 1.0}
            )
        for tag in tags:
            concept_id = f"concept:{slug(tag)}"
            artifacts.append({"@id": concept_id, "@type": "Concept", "name": tag})
            relationships.append(
                {"source": paper_id, "predicate": "mentions", "target": concept_id, "confidence": 1.0}
            )

    for connection in corpus.get("connections", []):
        source, target = str(connection.get("source_id", "")), str(connection.get("target_id", ""))
        if source in article_ids and target in article_ids:
            relationships.append(
                {
                    "source": f"paper:{source}",
                    "predicate": "derivedFrom",
                    "target": f"paper:{target}",
                    "confidence": connection.get("strength", 0.5),
                    "note": connection.get("description", ""),
                }
            )
    return artifacts, relationships


def extract_roadmap_artifact(path: Path, root: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    title = path.stem.replace("_", " ").title()
    source = {"file": repo_relative(path, root), "line": 1}
    return [
        {
            "@id": f"roadmap:{slug(path.stem)}",
            "@type": "Roadmap",
            "name": title,
            "source": source,
            "summary": "Versioned project roadmap; its phases and decisions are primary research artifacts.",
            "tags": ["roadmap", "research"],
        }
    ]


def unique_by_id(artifacts: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    merged: dict[str, dict[str, Any]] = {}
    for artifact in artifacts:
        artifact_id = artifact["@id"]
        if artifact_id not in merged:
            merged[artifact_id] = artifact
            continue
        # Corpus records can introduce the same author/concept many times.  The
        # first record carries its canonical spelling; later records may enrich it.
        for key, value in artifact.items():
            if key not in merged[artifact_id] or merged[artifact_id][key] in (None, "", [], {}):
                merged[artifact_id][key] = value
    return [merged[key] for key in sorted(merged)]


def unique_relationships(relationships: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[tuple[str, str, str]] = set()
    output: list[dict[str, Any]] = []
    for relationship in relationships:
        key = (relationship["source"], relationship["predicate"], relationship["target"])
        if key not in seen:
            seen.add(key)
            output.append(relationship)
    return sorted(output, key=lambda item: (item["source"], item["predicate"], item["target"]))


def apply_curation(
    artifacts: list[dict[str, Any]], relationships: list[dict[str, Any]], curation: dict[str, Any]
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Merge explicit bibliographic corrections after corpus de-duplication."""
    by_id = {artifact["@id"]: dict(artifact) for artifact in artifacts}
    for artifact in curation.get("artifacts", []):
        if not isinstance(artifact, dict) or not artifact.get("@id"):
            raise ValueError("each curated artifact needs an @id")
        existing = by_id.get(artifact["@id"], {})
        by_id[artifact["@id"]] = {**existing, **artifact}
    for artifact_id, override in curation.get("overrides", {}).items():
        if artifact_id not in by_id:
            raise ValueError(f"curation override references unknown artifact {artifact_id}")
        if not isinstance(override, dict):
            raise ValueError(f"curation override for {artifact_id} is not an object")
        by_id[artifact_id].update(override)
    return (
        [by_id[artifact_id] for artifact_id in sorted(by_id)],
        unique_relationships([*relationships, *curation.get("relationships", [])]),
    )


def build_registry(args: argparse.Namespace) -> dict[str, Any]:
    root = args.repo_root.resolve()
    corpus = load_corpus((root / args.corpus).resolve())
    corpus_artifacts, corpus_relationships = extract_corpus_artifacts(corpus)
    paper_artifacts, paper_relationships = load_paper_artifacts((root / args.paper_root).resolve(), root)
    known_papers = {str(article["id"]) for article in corpus.get("articles", []) if article.get("id")}
    known_papers.update(
        str(artifact.get("arxivId"))
        for artifact in paper_artifacts
        if artifact.get("@type") == "SourcePaper" and artifact.get("arxivId")
    )
    lean_artifacts, lean_relationships = extract_lean_artifacts(
        (root / args.lean_root).resolve(), root, known_papers
    )
    roadmap_artifacts = extract_roadmap_artifact((root / args.roadmap).resolve(), root)
    artifacts = unique_by_id([*corpus_artifacts, *lean_artifacts, *roadmap_artifacts])
    relationships = unique_relationships([*corpus_relationships, *lean_relationships])
    curation = load_curation((root / args.curation).resolve())
    curation = {
        **curation,
        "artifacts": [*curation.get("artifacts", []), *paper_artifacts],
        "relationships": [*curation.get("relationships", []), *paper_relationships],
    }
    artifacts, relationships = apply_curation(artifacts, relationships, curation)
    return {
        "@context": CONTEXT,
        "registryVersion": 1,
        "@graph": artifacts,
        "relationships": relationships,
        "statistics": {
            "artifacts": len(artifacts),
            "relationships": len(relationships),
            "byType": dict(sorted(Counter(item["@type"] for item in artifacts).items())),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--lean-root", type=Path, default=DEFAULT_LEAN_ROOT)
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--roadmap", type=Path, default=DEFAULT_ROADMAP)
    parser.add_argument("--curation", type=Path, default=DEFAULT_CURATION)
    parser.add_argument("--paper-root", type=Path, default=DEFAULT_PAPER_ROOT)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true", help="fail if the output would change")
    args = parser.parse_args()

    registry = build_registry(args)
    output = (args.repo_root / args.output).resolve()
    rendered = json.dumps(registry, indent=2, ensure_ascii=False) + "\n"
    if args.check:
        if not output.exists() or output.read_text(encoding="utf-8") != rendered:
            print(f"artifact registry is stale: {repo_relative(output, args.repo_root)}", file=sys.stderr)
            return 1
        print(f"artifact registry is current ({registry['statistics']['artifacts']} artifacts)")
        return 0
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(rendered, encoding="utf-8")
    print(
        f"wrote {repo_relative(output, args.repo_root)}: "
        f"{registry['statistics']['artifacts']} artifacts, {registry['statistics']['relationships']} relationships"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
