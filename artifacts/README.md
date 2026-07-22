# Artifact registry

`registry.jsonld` is generated from versioned project inputs:

- `proofs/` (or a selected Lean source root) for formal declarations;
- `dataset/extracted/rh_corpus_database_complete.json` for papers, authors,
  concepts, and extracted paper relationships; and
- `curation.json` for a deliberately small set of source-verified author-name
  corrections and public bibliographic references; and
- optional Markdown roots for roadmaps, research gates, and decisions.

Regenerate the checked-in registry from the repository root:

```bash
python3 scripts/ingest-artifacts.py
python3 scripts/build-artifact-index.py --validate
python3 scripts/export-artifact-registry.py
```

The SQLite index is deliberately ignored. It is a reproducible local query
cache, while JSON-LD is the portable, reviewable source of truth.

## Public bibliography policy

The corpus includes legacy shorthand author names and occasional collective or
unknown-author placeholders. `curation.json` does not erase those records; it
adds or corrects only the named people and references that are source-verified
and safe to show in the public reference ledger. The static-site copy is made
with `scripts/export-artifact-registry.py`, so the website never invents a
separate bibliography.
