# Artifact registry

`registry.jsonld` is generated from versioned project inputs:

- `proofs/` (or a selected Lean source root) for formal declarations;
- `dataset/extracted/rh_corpus_database_complete.json` for papers, authors,
  concepts, and extracted paper relationships; and
- optional Markdown roots for roadmaps, research gates, and decisions.

Regenerate the checked-in registry from the repository root:

```bash
python3 scripts/ingest-artifacts.py
python3 scripts/build-artifact-index.py --validate
```

The SQLite index is deliberately ignored. It is a reproducible local query
cache, while JSON-LD is the portable, reviewable source of truth.
