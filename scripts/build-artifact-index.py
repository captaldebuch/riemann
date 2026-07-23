#!/usr/bin/env python3
"""Build and validate the local SQLite index for the JSON-LD artifact registry."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import sqlite3
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_REGISTRY = Path("artifacts/registry.jsonld")
DEFAULT_DATABASE = Path("artifacts/artifacts.sqlite")

PAPER_CLAIM_STATUSES = {"sound", "conditional", "scope_mismatch", "unsupported", "contradicted", "unreviewed"}
PAPER_CLAIM_METHODS = {
    "source-reading", "hypothesis-check", "definition-check", "formalization-check",
    "numerical-check", "counterexample", "external-erratum",
}


def load_registry(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data.get("@graph"), list) or not isinstance(data.get("relationships"), list):
        raise ValueError("registry must contain JSON-LD @graph and relationships arrays")
    return data


def validate_registry(registry: dict[str, Any], root: Path) -> list[str]:
    errors: list[str] = []
    artifact_ids: set[str] = set()
    artifact_types: dict[str, str] = {}
    for artifact in registry["@graph"]:
        artifact_id = artifact.get("@id")
        if not isinstance(artifact_id, str) or not artifact_id:
            errors.append("artifact without a nonempty @id")
            continue
        if artifact_id in artifact_ids:
            errors.append(f"duplicate artifact id: {artifact_id}")
        artifact_ids.add(artifact_id)
        artifact_types[artifact_id] = str(artifact.get("@type", ""))
        if not isinstance(artifact.get("@type"), str):
            errors.append(f"artifact {artifact_id} has no @type")
        if not isinstance(artifact.get("name"), str) or not artifact["name"].strip():
            errors.append(f"artifact {artifact_id} has no name")
        source = artifact.get("source")
        if source and source.get("file"):
            file_path = root / source["file"]
            if not file_path.exists():
                errors.append(f"artifact {artifact_id} references missing source file {source['file']}")
            if source.get("line") is not None and source["line"] < 1:
                errors.append(f"artifact {artifact_id} has an invalid source line")

        paper_claims = artifact.get("paperClaims", [])
        if not isinstance(paper_claims, list):
            errors.append(f"artifact {artifact_id} has non-list paperClaims")
            continue
        for index, paper_claim in enumerate(paper_claims, start=1):
            prefix = f"artifact {artifact_id} paper claim {index}"
            if not isinstance(paper_claim, dict):
                errors.append(f"{prefix} is not an object")
                continue
            if not isinstance(paper_claim.get("sourcePaper"), str) or not paper_claim["sourcePaper"].startswith("paper:"):
                errors.append(f"{prefix} has no paper: sourcePaper")
            if not isinstance(paper_claim.get("claim"), str) or not paper_claim["claim"].strip():
                errors.append(f"{prefix} has no claim text")
            validity = paper_claim.get("validity")
            if not isinstance(validity, dict):
                errors.append(f"{prefix} has no validity review")
                continue
            status = validity.get("status")
            if status not in PAPER_CLAIM_STATUSES:
                errors.append(f"{prefix} has invalid validity status {status!r}")
            methods = validity.get("method")
            if not isinstance(methods, list) or not methods or any(method not in PAPER_CLAIM_METHODS for method in methods):
                errors.append(f"{prefix} has invalid review method")
            reviewed_at = validity.get("reviewedAt")
            try:
                dt.date.fromisoformat(str(reviewed_at))
            except ValueError:
                errors.append(f"{prefix} has invalid review date")
            if not isinstance(validity.get("note"), str) or not validity["note"].strip():
                errors.append(f"{prefix} has no review note")
            if status == "conditional" and not validity.get("conditions"):
                errors.append(f"{prefix} is conditional but has no explicit conditions")

    for artifact in registry["@graph"]:
        for paper_claim in artifact.get("paperClaims", []):
            if not isinstance(paper_claim, dict):
                continue
            source_paper = paper_claim.get("sourcePaper")
            if source_paper not in artifact_ids or artifact_types.get(source_paper) != "SourcePaper":
                errors.append(f"artifact {artifact.get('@id')} references unknown source paper {source_paper!r}")

    for relationship in registry["relationships"]:
        source, predicate, target = (
            relationship.get("source"),
            relationship.get("predicate"),
            relationship.get("target"),
        )
        if source not in artifact_ids:
            errors.append(f"relationship source is missing: {source}")
        if target not in artifact_ids:
            errors.append(f"relationship target is missing: {target}")
        if not isinstance(predicate, str) or not predicate:
            errors.append(f"relationship {source!r} -> {target!r} has no predicate")
        if predicate == "derivedFrom" and artifact_types.get(target) == "SourcePaper":
            artifact = next((item for item in registry["@graph"] if item.get("@id") == source), None)
            claims = artifact.get("paperClaims", []) if artifact else []
            if not any(claim.get("sourcePaper") == target for claim in claims if isinstance(claim, dict)):
                errors.append(f"paper-derived artifact {source} has no matching paperClaims review for {target}")
    return errors


def create_schema(connection: sqlite3.Connection) -> None:
    connection.executescript(
        """
        PRAGMA foreign_keys = ON;
        DROP TABLE IF EXISTS relationships;
        DROP TABLE IF EXISTS artifacts;
        DROP TABLE IF EXISTS metadata;

        CREATE TABLE artifacts (
          id TEXT PRIMARY KEY,
          type TEXT NOT NULL,
          name TEXT NOT NULL,
          statement TEXT,
          source_file TEXT,
          source_line INTEGER,
          verification_status TEXT,
          difficulty TEXT,
          open_problem INTEGER,
          payload_json TEXT NOT NULL
        );
        CREATE INDEX artifacts_type_name_idx ON artifacts(type, name);
        CREATE INDEX artifacts_source_idx ON artifacts(source_file, source_line);

        CREATE TABLE relationships (
          source_id TEXT NOT NULL REFERENCES artifacts(id) ON DELETE CASCADE,
          predicate TEXT NOT NULL,
          target_id TEXT NOT NULL REFERENCES artifacts(id) ON DELETE CASCADE,
          confidence REAL,
          note TEXT,
          PRIMARY KEY (source_id, predicate, target_id)
        );
        CREATE INDEX relationships_target_idx ON relationships(target_id, predicate);
        CREATE INDEX relationships_source_idx ON relationships(source_id, predicate);

        CREATE TABLE metadata (
          key TEXT PRIMARY KEY,
          value TEXT NOT NULL
        );
        """
    )


def build_index(registry: dict[str, Any], database: Path) -> None:
    database.parent.mkdir(parents=True, exist_ok=True)
    with sqlite3.connect(database) as connection:
        create_schema(connection)
        connection.executemany(
            """
            INSERT INTO artifacts (
              id, type, name, statement, source_file, source_line,
              verification_status, difficulty, open_problem, payload_json
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            """,
            [
                (
                    item["@id"],
                    item["@type"],
                    item["name"],
                    item.get("statement"),
                    item.get("source", {}).get("file"),
                    item.get("source", {}).get("line"),
                    item.get("verification", {}).get("status"),
                    item.get("difficulty"),
                    int(bool(item.get("openProblem", False))),
                    json.dumps(item, ensure_ascii=False, sort_keys=True),
                )
                for item in registry["@graph"]
            ],
        )
        connection.executemany(
            """
            INSERT INTO relationships (source_id, predicate, target_id, confidence, note)
            VALUES (?, ?, ?, ?, ?)
            """,
            [
                (
                    edge["source"],
                    edge["predicate"],
                    edge["target"],
                    edge.get("confidence"),
                    edge.get("note"),
                )
                for edge in registry["relationships"]
            ],
        )
        connection.executemany(
            "INSERT INTO metadata (key, value) VALUES (?, ?)",
            [
                ("registryVersion", str(registry.get("registryVersion", ""))),
                ("sourceRevision", str(registry.get("sourceRevision", ""))),
                ("statistics", json.dumps(registry.get("statistics", {}), sort_keys=True)),
            ],
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument("--database", type=Path, default=DEFAULT_DATABASE)
    parser.add_argument("--validate", action="store_true", help="validate only; do not write SQLite")
    args = parser.parse_args()

    registry_path = (args.repo_root / args.registry).resolve()
    try:
        registry = load_registry(registry_path)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"cannot load registry: {error}", file=sys.stderr)
        return 2

    errors = validate_registry(registry, args.repo_root.resolve())
    if errors:
        print("artifact registry validation failed:", file=sys.stderr)
        for error in errors:
            print(f"  - {error}", file=sys.stderr)
        return 1
    if args.validate:
        print(
            f"registry valid: {len(registry['@graph'])} artifacts, "
            f"{len(registry['relationships'])} relationships"
        )
        return 0
    database_path = (args.repo_root / args.database).resolve()
    build_index(registry, database_path)
    print(
        f"indexed {len(registry['@graph'])} artifacts and {len(registry['relationships'])} relationships "
        f"into {database_path.relative_to(args.repo_root.resolve())}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
