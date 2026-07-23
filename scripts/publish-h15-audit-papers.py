#!/usr/bin/env python3
"""Publish the audited H15 PDFs into the static website tree.

The individual JSON-LD records under ``artifacts/papers`` are the manifest.
This script copies only their declared local PDFs to the public site and can
verify that the public files are byte-for-byte current.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PAPER_ROOT = Path("artifacts/papers")
DEFAULT_DESTINATION = Path("website/html/papers/h15-audit")


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


def audit_sources(root: Path, paper_root: Path) -> list[Path]:
    sources: list[Path] = []
    for path in sorted(paper_root.glob("*.json")):
        with path.open(encoding="utf-8") as handle:
            paper = json.load(handle)
        local_pdf = paper.get("pdfLocal")
        if not isinstance(local_pdf, str) or not local_pdf:
            raise ValueError(f"{path.relative_to(root)} has no pdfLocal value")
        source = (root / local_pdf).resolve()
        if not source.is_file() or not is_pdf(source):
            raise ValueError(f"{path.relative_to(root)} references an invalid PDF: {local_pdf}")
        sources.append(source)
    if len(sources) != len({source.name for source in sources}):
        raise ValueError("audit PDF filenames must be unique")
    return sources


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--paper-root", type=Path, default=DEFAULT_PAPER_ROOT)
    parser.add_argument("--destination", type=Path, default=DEFAULT_DESTINATION)
    parser.add_argument("--check", action="store_true", help="fail if public copies are missing or stale")
    args = parser.parse_args()

    root = args.repo_root.resolve()
    sources = audit_sources(root, (root / args.paper_root).resolve())
    destination = (root / args.destination).resolve()
    stale = [source for source in sources if not (destination / source.name).is_file() or file_hash(source) != file_hash(destination / source.name)]
    if args.check and stale:
        raise SystemExit("published audit PDFs are stale: " + ", ".join(source.name for source in stale))
    if not args.check:
        destination.mkdir(parents=True, exist_ok=True)
        for source in stale:
            shutil.copyfile(source, destination / source.name)
    action = "checked" if args.check else "published"
    print(f"{action} {len(sources)} H15 audit PDFs; {len(stale)} copied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
