#!/usr/bin/env python3
"""Publish all linked corpus PDFs into the static website tree.

The canonical 78-entry corpus metadata identifies 62 distinct local source
PDFs. This script mirrors exactly those referenced files, preserving the
metadata-to-file relationship used by the public catalogue.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = Path("dataset/extracted/rh_corpus_database_complete.json")
DEFAULT_SOURCE_DIRECTORY = Path("dataset/corpus")
DEFAULT_DESTINATION = Path("website/html/papers/corpus")


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def is_pdf(path: Path) -> bool:
    """Check the file signature without loading a source PDF into memory."""
    try:
        with path.open("rb") as handle:
            return handle.read(5) == b"%PDF-"
    except OSError:
        return False


def corpus_sources(corpus_path: Path, source_directory: Path) -> list[Path]:
    with corpus_path.open(encoding="utf-8") as handle:
        payload = json.load(handle)
    articles = payload.get("articles")
    if not isinstance(articles, list):
        raise ValueError("corpus dataset must contain an articles array")
    filenames = sorted({article.get("local_pdf_path") for article in articles if isinstance(article, dict) and article.get("local_pdf_path")})
    if len(filenames) != 62:
        raise ValueError(f"expected 62 distinct linked corpus PDFs, found {len(filenames)}")
    sources = [(source_directory / filename).resolve() for filename in filenames]
    invalid = [source.name for source in sources if not source.is_file() or not is_pdf(source)]
    if invalid:
        raise ValueError("missing or invalid corpus PDFs: " + ", ".join(invalid))
    return sources


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--corpus", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--source-directory", type=Path, default=DEFAULT_SOURCE_DIRECTORY)
    parser.add_argument("--destination", type=Path, default=DEFAULT_DESTINATION)
    parser.add_argument("--check", action="store_true", help="fail if public copies are missing or stale")
    args = parser.parse_args()

    root = args.repo_root.resolve()
    sources = corpus_sources((root / args.corpus).resolve(), (root / args.source_directory).resolve())
    destination = (root / args.destination).resolve()
    stale = [source for source in sources if not (destination / source.name).is_file() or file_hash(source) != file_hash(destination / source.name)]
    if args.check and stale:
        raise SystemExit("published corpus PDFs are stale: " + ", ".join(source.name for source in stale))
    if not args.check:
        destination.mkdir(parents=True, exist_ok=True)
        for source in stale:
            shutil.copyfile(source, destination / source.name)
    action = "checked" if args.check else "published"
    print(f"{action} {len(sources)} corpus PDFs; {len(stale)} copied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
