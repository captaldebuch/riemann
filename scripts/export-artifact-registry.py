#!/usr/bin/env python3
"""Copy the versioned artifact registry into the static website payload.

The checked-in JSON-LD file under ``artifacts/`` is the source of truth.  The
website receives an exact copy so it works on GitHub Pages and other static
hosts, which cannot reach files outside the published ``website/html`` tree.
"""

from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE = Path("artifacts/registry.jsonld")
DEFAULT_DESTINATION = Path("website/html/data/artifacts/registry.jsonld")


def validate(path: Path) -> tuple[int, int]:
    """Return artifact and relationship totals after a minimal payload check."""
    with path.open(encoding="utf-8") as handle:
        registry = json.load(handle)
    graph = registry.get("@graph")
    relationships = registry.get("relationships")
    if not isinstance(graph, list) or not isinstance(relationships, list):
        raise ValueError("registry must contain list-valued @graph and relationships")
    return len(graph), len(relationships)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    parser.add_argument("--destination", type=Path, default=DEFAULT_DESTINATION)
    parser.add_argument("--check", action="store_true", help="verify the published copy is current")
    args = parser.parse_args()

    root = args.repo_root.resolve()
    source = (root / args.source).resolve()
    destination = (root / args.destination).resolve()
    artifacts, relationships = validate(source)

    if args.check:
        if not destination.exists():
            raise SystemExit(f"published registry is missing: {destination.relative_to(root)}")
        validate(destination)
        if source.read_bytes() != destination.read_bytes():
            raise SystemExit("published registry is stale; run export-artifact-registry.py")
        print(f"published registry is current: {artifacts} artifacts, {relationships} relationships")
        return 0

    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    print(f"published {artifacts} artifacts and {relationships} relationships to {destination.relative_to(root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
