# Artifact registry

`registry.jsonld` is generated from versioned project inputs:

- `proofs/` (or a selected Lean source root) for formal declarations;
- `dataset/extracted/rh_corpus_database_complete.json` for papers, authors,
  concepts, and extracted paper relationships; and
- `curation.json` for a deliberately small set of source-verified author-name
  corrections and public bibliographic references; and
- `papers/*.json` for individually reviewed source-paper records, including
  explicit H15 audit statuses and research-role notes; and
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

## Paper-claim validity policy

A source-paper link is not proof evidence by itself. When an artifact imports,
translates, or applies a paper claim, it carries a `paperClaims` review with a
source location, review method, and an explicit outcome. The full workflow and
status meanings are in `PAPER_CLAIM_VALIDITY_PROTOCOL.md`.

Only a `derivedFrom` relation to a `SourcePaper` represents this stronger kind
of use. Registry validation requires a matching review. `informs` and
`motivatedBy` remain relevance links and make no validity claim.

## H15 paper-audit records

`artifacts/papers/` contains one JSON-LD record per acquired audit paper and a
checked-in manifest. Each record has a bibliographic source URL, local PDF path,
audit status (`reviewed`, `pending`, or `rejected`), and roles in H15. The
`informs` relationships generated from these records preserve a paper’s
research relevance without claiming that it proves a formal declaration.

`scripts/publish-h15-audit-papers.py` mirrors all of these PDFs into
`website/html/papers/h15-audit/`; the Artifact Explorer exposes a download link
only after that checked-in website copy is current.
