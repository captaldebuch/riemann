#!/usr/bin/env python3
"""Publish the complete corpus inventory for the static public catalogue.

The source metadata under ``dataset/extracted`` contains all 78 intended
corpus entries.  The website receives a normalized copy with stable IDs for
records whose original identifier is absent, plus a truthful local-PDF status.
Bibliographic corrections are sourced from a small, reviewable transcription
map created from the title-bearing pages of the local PDFs.  It deliberately
does not manufacture author names, abstracts, or file links.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = Path("dataset/extracted/rh_corpus_database_complete.json")
DEFAULT_PROCESSED = Path("website/html/rh_corpus_database.json")
DEFAULT_PDF_DIRECTORY = Path("dataset/corpus")
DEFAULT_BIBLIOGRAPHY = Path("dataset/extracted/corpus_pdf_bibliography.json")
DEFAULT_DESTINATION = Path("website/html/data/corpus-inventory.json")


def article_id(article: dict[str, object], position: int, used: set[str]) -> str:
    """Give every public record a stable, unique identifier."""
    raw = article.get("id")
    base = str(raw).strip() if raw is not None and str(raw).strip() else f"catalogue-{position:03d}"
    candidate = base
    suffix = 2
    while candidate in used:
        candidate = f"{base}-{suffix}"
        suffix += 1
    used.add(candidate)
    return candidate


def author_names(article: dict[str, object]) -> list[str]:
    """Preserve author labels exactly as supplied by the source metadata."""
    names: list[str] = []
    for author in article.get("authors", []):
        if isinstance(author, dict) and isinstance(author.get("name"), str):
            names.append(author["name"])
        elif isinstance(author, str):
            names.append(author)
    return names


def validate_payload(payload: dict[str, object]) -> tuple[list[dict[str, object]], int]:
    articles = payload.get("articles")
    if not isinstance(articles, list) or not all(isinstance(article, dict) for article in articles):
        raise ValueError("source payload must contain a list-valued articles field")
    if len(articles) != 78:
        raise ValueError(f"expected 78 source records, found {len(articles)}")
    return articles, len(articles)


def load_bibliography(source: Path, referenced_pdfs: set[str]) -> dict[str, dict[str, object]]:
    """Load only explicit, source-reviewable PDF title-page transcriptions."""
    with source.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    entries = payload.get("byPdf")
    if not isinstance(entries, dict):
        raise ValueError("bibliography payload must contain an object-valued byPdf field")

    normalized: dict[str, dict[str, object]] = {}
    for pdf_name, entry in entries.items():
        if not isinstance(pdf_name, str) or not isinstance(entry, dict):
            raise ValueError("bibliography entries must map PDF filenames to objects")
        title = entry.get("title")
        authors = entry.get("authors")
        status = entry.get("status", "transcribed")
        if not isinstance(title, str) or not title.strip():
            raise ValueError(f"bibliography entry for {pdf_name!r} has no title")
        if not isinstance(authors, list) or not all(isinstance(author, str) and author.strip() for author in authors):
            raise ValueError(f"bibliography entry for {pdf_name!r} has invalid authors")
        if status not in {"transcribed", "needs-review"}:
            raise ValueError(f"bibliography entry for {pdf_name!r} has an invalid status")
        normalized[pdf_name] = {
            "title": title.strip(),
            "authors": [author.strip() for author in authors],
            "status": status,
        }

    missing = referenced_pdfs - set(normalized)
    if missing:
        raise ValueError("bibliography map is missing source PDFs: " + ", ".join(sorted(missing)))
    extra = set(normalized) - referenced_pdfs
    if extra:
        raise ValueError("bibliography map contains unreferenced PDFs: " + ", ".join(sorted(extra)))
    return normalized


def build_inventory(
    source: Path, processed: Path, pdf_directory: Path, bibliography: Path
) -> dict[str, object]:
    with source.open(encoding="utf-8") as handle:
        articles, total = validate_payload(json.load(handle))
    with processed.open(encoding="utf-8") as handle:
        processed_payload = json.load(handle)

    processed_ids = {
        str(article["id"])
        for article in processed_payload.get("articles", [])
        if isinstance(article, dict) and article.get("id") is not None
    }
    pdf_references = Counter(
        str(article["local_pdf_path"])
        for article in articles
        if isinstance(article.get("local_pdf_path"), str)
        and (pdf_directory / str(article["local_pdf_path"])).is_file()
    )
    bibliography_by_pdf = load_bibliography(bibliography, set(pdf_references))
    stored_pdf_files = {
        path.name
        for path in pdf_directory.rglob("*")
        if path.is_file() and path.suffix.lower() == ".pdf"
    }
    used_ids: set[str] = set()
    seen_pdf_references: set[str] = set()
    records: list[dict[str, object]] = []

    for position, article in enumerate(articles, start=1):
        source_id = article.get("id")
        source_id_text = str(source_id) if source_id is not None else None
        pdf_name = article.get("local_pdf_path")
        pdf_name_text = str(pdf_name) if isinstance(pdf_name, str) and pdf_name else None
        local_pdf = bool(pdf_name_text and (pdf_directory / pdf_name_text).is_file())
        shared_source = bool(pdf_name_text and pdf_references[pdf_name_text] > 1)
        first_reference = not pdf_name_text or pdf_name_text not in seen_pdf_references
        if pdf_name_text:
            seen_pdf_references.add(pdf_name_text)
        bibliographic_entry = bibliography_by_pdf.get(pdf_name_text) if pdf_name_text else None
        if bibliographic_entry:
            bibliographic_status = str(bibliographic_entry["status"])
            bibliography_source = (
                "PDF title page"
                if bibliographic_status == "transcribed"
                else "Archive scan — author attribution needs review"
            )
            title = bibliographic_entry["title"]
            authors = bibliographic_entry["authors"]
        else:
            bibliographic_status = "catalogue-metadata"
            bibliography_source = "Catalogue metadata"
            title = article.get("title") or "Untitled corpus record"
            authors = author_names(article)
        records.append(
            {
                "id": article_id(article, position, used_ids),
                "sourceId": source_id_text,
                "title": title,
                "authors": authors,
                "year": article.get("year"),
                "role": article.get("role_in_project") or "Unclassified",
                "tags": article.get("tags") if isinstance(article.get("tags"), list) else [],
                "journal": article.get("journal"),
                "doi": article.get("doi"),
                "arxivId": article.get("arxiv_id"),
                "processed": source_id_text in processed_ids,
                "localPdf": local_pdf,
                "localPdfName": pdf_name_text,
                "publishedPdf": f"papers/corpus/{pdf_name_text}" if local_pdf and pdf_name_text else None,
                "sharedSource": shared_source,
                "firstSourceReference": first_reference,
                "bibliographySource": bibliography_source,
                "bibliographyStatus": bibliographic_status,
            }
        )

    referenced_pdfs = set(pdf_references)
    processed_records = sum(record["processed"] for record in records)
    return {
        "version": 2,
        "source": "dataset/extracted/rh_corpus_database_complete.json",
        "bibliography": "dataset/extracted/corpus_pdf_bibliography.json",
        "records": records,
        "summary": {
            "metadataRecords": total,
            "processedRecords": processed_records,
            "referencedSourcePdfs": len(referenced_pdfs),
            "duplicateMetadataEntries": total - len(referenced_pdfs),
            "unindexedPdfFiles": len(stored_pdf_files - referenced_pdfs),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--processed", type=Path, default=DEFAULT_PROCESSED)
    parser.add_argument("--pdf-directory", type=Path, default=DEFAULT_PDF_DIRECTORY)
    parser.add_argument("--bibliography", type=Path, default=DEFAULT_BIBLIOGRAPHY)
    parser.add_argument("--destination", type=Path, default=DEFAULT_DESTINATION)
    parser.add_argument("--check", action="store_true", help="verify the published inventory is current")
    args = parser.parse_args()

    root = args.repo_root.resolve()
    inventory = build_inventory(
        (root / args.source).resolve(),
        (root / args.processed).resolve(),
        (root / args.pdf_directory).resolve(),
        (root / args.bibliography).resolve(),
    )
    rendered = json.dumps(inventory, ensure_ascii=False, indent=2) + "\n"
    destination = (root / args.destination).resolve()

    if args.check:
        if not destination.exists() or destination.read_text(encoding="utf-8") != rendered:
            raise SystemExit("published corpus inventory is stale; run export-corpus-inventory.py")
        print(
            "published corpus inventory is current: "
            f"{inventory['summary']['metadataRecords']} records, "
            f"{inventory['summary']['referencedSourcePdfs']} distinct linked PDFs"
        )
        return 0

    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(rendered, encoding="utf-8")
    print(
        "published corpus inventory: "
        f"{inventory['summary']['metadataRecords']} records, "
        f"{inventory['summary']['processedRecords']} processed, "
        f"{inventory['summary']['referencedSourcePdfs']} distinct linked PDFs"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
