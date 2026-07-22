#!/usr/bin/env python3
"""Query the local artifact SQLite index.

Examples:
  python3 scripts/query-artifacts.py --paper 1211.5191 --from papers --to theorems
  python3 scripts/query-artifacts.py --proof-dag theorem:NB5.foo --depth 3
  python3 scripts/query-artifacts.py --open-problems --difficulty RH-strength
"""

from __future__ import annotations

import argparse
import json
import sqlite3
import sys
from collections import deque
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_DATABASE = Path("artifacts/artifacts.sqlite")


def normalized_id(value: str, prefix: str | None = None) -> str:
    if ":" in value or prefix is None:
        return value
    return f"{prefix}:{value}"


def resolve_formal_id(connection: sqlite3.Connection, value: str) -> str:
    """Accept an artifact id, an exact formal name, or a bare theorem name."""
    if ":" in value:
        return value
    for candidate in (value, f"theorem:{value}", f"lemma:{value}", f"axiom:{value}"):
        if connection.execute("SELECT 1 FROM artifacts WHERE id = ?", (candidate,)).fetchone():
            return candidate
    rows = connection.execute(
        "SELECT id FROM artifacts WHERE name = ? OR name LIKE ? ORDER BY id",
        (value, f"%.{value}"),
    ).fetchall()
    return rows[0]["id"] if len(rows) == 1 else value


def row_to_artifact(row: sqlite3.Row) -> dict[str, Any]:
    return json.loads(row["payload_json"])


def display(items: list[dict[str, Any]], as_json: bool) -> None:
    if as_json:
        print(json.dumps(items, indent=2, ensure_ascii=False))
        return
    if not items:
        print("No matching artifacts.")
        return
    for item in items:
        source = item.get("source", {})
        location = ""
        if source.get("file"):
            location = f" — {source['file']}:{source.get('line', '?')}"
        print(f"{item['@id']} [{item['@type']}] {item['name']}{location}")


def artifact_by_id(connection: sqlite3.Connection, artifact_id: str) -> dict[str, Any] | None:
    row = connection.execute("SELECT * FROM artifacts WHERE id = ?", (artifact_id,)).fetchone()
    return row_to_artifact(row) if row else None


def theorem_results_for_paper(connection: sqlite3.Connection, paper_id: str) -> list[dict[str, Any]]:
    rows = connection.execute(
        """
        SELECT a.* FROM relationships r
        JOIN artifacts a ON a.id = r.source_id
        WHERE r.target_id = ? AND r.predicate IN ('motivatedBy', 'formalizes')
          AND a.type IN ('FormalTheorem', 'FormalLemma', 'FormalAxiom')
        ORDER BY a.name
        """,
        (paper_id,),
    ).fetchall()
    return [row_to_artifact(row) for row in rows]


def proof_dag(connection: sqlite3.Connection, start: str, depth: int) -> list[dict[str, Any]]:
    queue: deque[tuple[str, int]] = deque([(start, 0)])
    visited: set[str] = set()
    output: list[dict[str, Any]] = []
    while queue:
        current, level = queue.popleft()
        if current in visited:
            continue
        visited.add(current)
        artifact = artifact_by_id(connection, current)
        if artifact is None:
            continue
        artifact["depth"] = level
        edges = connection.execute(
            """
            SELECT predicate, target_id FROM relationships
            WHERE source_id = ? AND predicate = 'dependsOn'
            ORDER BY target_id
            """,
            (current,),
        ).fetchall()
        artifact["dependencies"] = [dict(edge) for edge in edges]
        output.append(artifact)
        if level < depth:
            queue.extend((edge["target_id"], level + 1) for edge in edges)
    return output


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--database", type=Path, default=DEFAULT_DATABASE)
    parser.add_argument("--id", help="look up one exact artifact identifier")
    parser.add_argument("--search", help="case-insensitive name search")
    parser.add_argument("--paper", help="paper id for a paper-to-theorem query")
    parser.add_argument("--from", dest="source_kind", choices=["papers", "theorems"])
    parser.add_argument("--to", dest="target_kind", choices=["papers", "theorems"])
    parser.add_argument("--gate-blocks", help="list gates that block an artifact id")
    parser.add_argument("--proof-dag", help="show dependsOn DAG from this artifact id")
    parser.add_argument("--depth", type=int, default=3)
    parser.add_argument("--open-problems", action="store_true")
    parser.add_argument("--difficulty")
    parser.add_argument("--json", action="store_true", help="emit JSON instead of concise text")
    args = parser.parse_args()

    database = (args.repo_root / args.database).resolve()
    if not database.exists():
        print("artifact index not found; run scripts/build-artifact-index.py first", file=sys.stderr)
        return 2
    with sqlite3.connect(database) as connection:
        connection.row_factory = sqlite3.Row
        if args.paper:
            if args.source_kind not in (None, "papers") or args.target_kind not in (None, "theorems"):
                parser.error("--paper currently supports --from papers --to theorems")
            display(theorem_results_for_paper(connection, normalized_id(args.paper, "paper")), args.json)
            return 0
        if args.proof_dag:
            display(proof_dag(connection, resolve_formal_id(connection, args.proof_dag), max(0, args.depth)), args.json)
            return 0
        if args.gate_blocks:
            target = resolve_formal_id(connection, args.gate_blocks)
            rows = connection.execute(
                """
                SELECT a.* FROM relationships r JOIN artifacts a ON a.id = r.source_id
                WHERE r.predicate = 'blockedBy' AND r.target_id = ? ORDER BY a.name
                """,
                (target,),
            ).fetchall()
            display([row_to_artifact(row) for row in rows], args.json)
            return 0
        if args.id:
            artifact = artifact_by_id(connection, args.id)
            display([artifact] if artifact else [], args.json)
            return 0
        if args.open_problems:
            query = "SELECT * FROM artifacts WHERE open_problem = 1"
            parameters: list[Any] = []
            if args.difficulty:
                query += " AND difficulty = ?"
                parameters.append(args.difficulty)
            query += " ORDER BY name"
            display([row_to_artifact(row) for row in connection.execute(query, parameters)], args.json)
            return 0
        if args.search:
            rows = connection.execute(
                "SELECT * FROM artifacts WHERE lower(name) LIKE ? ORDER BY name", (f"%{args.search.lower()}%",)
            ).fetchall()
            display([row_to_artifact(row) for row in rows], args.json)
            return 0
    parser.error("choose a query mode; run with --help for examples")
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
