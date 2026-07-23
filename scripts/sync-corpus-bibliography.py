#!/usr/bin/env python3
"""Synchronize reviewed PDF title-page metadata into corpus dataset exports.

The bibliography map is the reviewable source of truth for title and personal
name transcription. This script updates only bibliographic fields in each
dataset export, retaining its different analytical, annotation, and processing
layers intact.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BIBLIOGRAPHY = Path("dataset/extracted/corpus_pdf_bibliography.json")
DEFAULT_DATASETS = (
    Path("dataset/extracted/rh_corpus_database_complete.json"),
    Path("website/html/rh_corpus_database.json"),
    Path("website/html/rh_corpus_database_complete.json"),
    Path("website/html/downloads/dataset_v1.json"),
)


def load_bibliography(path: Path) -> dict[str, dict[str, object]]:
    """Load normalized title/author transcriptions keyed by local PDF filename."""
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    entries = payload.get("byPdf")
    if not isinstance(entries, dict):
        raise ValueError("bibliography payload must contain an object-valued byPdf field")
    return entries


def rendered_dataset(path: Path, bibliography: dict[str, dict[str, object]]) -> str:
    """Return the dataset with only source-supported bibliographic fields replaced."""
    with path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    articles = payload.get("articles")
    if not isinstance(articles, list) or not all(isinstance(article, dict) for article in articles):
        raise ValueError(f"{path} must contain an articles array")

    for article in articles:
        pdf_name = article.get("local_pdf_path")
        if not isinstance(pdf_name, str) or pdf_name not in bibliography:
            continue
        entry = bibliography[pdf_name]
        title = entry.get("title")
        authors = entry.get("authors")
        status = entry.get("status", "transcribed")
        if not isinstance(title, str) or not isinstance(authors, list):
            raise ValueError(f"invalid bibliography entry for {pdf_name}")
        article["title"] = title
        article["authors"] = [{"name": author, "affiliation": None} for author in authors]
        article["bibliography_source"] = (
            "PDF title page" if status == "transcribed" else "Archive scan — author attribution needs review"
        )
        article["bibliography_status"] = status

    return json.dumps(payload, ensure_ascii=False, indent=2) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--bibliography", type=Path, default=DEFAULT_BIBLIOGRAPHY)
    parser.add_argument("--dataset", action="append", type=Path, dest="datasets")
    parser.add_argument("--check", action="store_true", help="fail when a dataset is out of sync")
    args = parser.parse_args()

    root = args.repo_root.resolve()
    bibliography = load_bibliography((root / args.bibliography).resolve())
    datasets = tuple(args.datasets) if args.datasets else DEFAULT_DATASETS
    stale: list[Path] = []
    for relative_path in datasets:
        path = (root / relative_path).resolve()
        rendered = rendered_dataset(path, bibliography)
        if path.read_text(encoding="utf-8") != rendered:
            stale.append(relative_path)
            if not args.check:
                path.write_text(rendered, encoding="utf-8")

    if args.check and stale:
        raise SystemExit("bibliographic dataset exports are stale: " + ", ".join(map(str, stale)))
    action = "checked" if args.check else "synchronized"
    print(f"{action} {len(datasets)} dataset exports; {len(stale)} changed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
