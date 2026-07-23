# The Riemann Hypothesis Corpus Dataset

A curated 78-entry metadata inventory spanning 160+ years of Riemann Hypothesis investigations, with extracted metadata and knowledge graphs.

## Current inventory audit

- **78 metadata entries** are present in `extracted/rh_corpus_database_complete.json`.
- They resolve to **62 distinct linked PDF files** in `corpus/`; **16 entries share** an already-linked source PDF.
- The archive holds **one additional PDF** that has not yet been assigned a complete metadata entry.
- **30 entries** have a separate processed research layer. The remaining entries are source-level metadata records.
- **75 entries** have titles and personal-name attributions transcribed from their linked PDF title pages; **3 entries** retain a recovered title but explicitly require author-attribution review because the archival scan does not support a reliable transcription.

The catalogue therefore distinguishes metadata entries from unique physical source files. It does not claim that all 78 entries are already independent, source-verified bibliographic records.

## Overview

- **78 Metadata Entries** — From classical analysis to modern spectral and probabilistic approaches
- **26 Key Mathematicians** — Detailed profiles and contributions
- **260+ Mathematical Concepts** — Keywords, intuitions, and formalizable elements
- **400+ Extracted Insights** — Historical development and proof strategies

## Contents

### `corpus/`
**Source PDF archive**

The archive contains 63 PDF files, 62 of which are currently linked from the 78-entry metadata inventory. The route breakdown below is historic planning metadata and should not be read as an independently audited count of unique PDFs.

Organized by mathematical route:

- **Analytic** (35 papers)
  - Classical Riemann–Hadamard approaches
  - Explicit formulas and bounds
  - Authors: Titchmarsh, Montgomery, Ivic, Conrey, etc.

- **Spectral** (12 papers)
  - Hilbert-Pólya perspective
  - Random matrix connections
  - Authors: Connes, Berry, Keating, etc.

- **Probabilistic** (18 papers)
  - Montgomery pair correlation
  - GUE hypothesis
  - Branching processes
  - Authors: Montgomery, Odlyzko, Forrester, etc.

- **Functional** (13 papers)
  - Nyman-Beurling criterion
  - Hardy space completeness
  - Dirichlet series methods
  - Authors: Beurling, Nyman, Burnol, etc.

### `extracted/`
**Processed Metadata & Knowledge Graphs**

#### `rh_corpus_database_complete.json`
```json
{
  "papers": {
    "arXiv:1211.5191": {
      "title": "Approximate Functional Equations for Dirichlet L-functions",
      "authors": ["Bettin", "Conrey", "Farmer"],
      "year": 2012,
      "category": "analytic",
      "key_novelties": [...],
      "formalizable_elements": [...],
      "concepts": [...],
      "intuitions": [...]
    }
  },
  "authors": {
    "Titchmarsh": {
      "full_name": "Edward Charles Titchmarsh",
      "birth_year": 1899,
      "bio": "...",
      "papers": ["arXiv:..."],
      "key_concepts": [...]
    }
  },
  "concepts": {
    "Riemann_Zeta_Function": {
      "description": "...",
      "papers": [...],
      "related_concepts": [...]
    }
  }
}
```

**Fields:**
- `title`, `authors`, `year` — Paper metadata; title and author values are synchronized from the reviewed PDF-title-page map where a linked local PDF exists
- `bibliography_source`, `bibliography_status` — Evidence and review status for the title/author transcription (`PDF title page`, or an explicitly marked archival-review case)
- `category` — One of: analytic, spectral, probabilistic, functional
- `key_novelties` — Main contributions
- `formalizable_elements` — What could be formalized in Lean
- `concepts` — Mathematical concepts (keywords)
- `intuitions` — Extracted mathematical insights

#### `corpus_pdf_bibliography.json`

**Reviewed title/author transcription map**

Maps each linked local PDF filename to its source-supported title and author list. It is the auditable bibliography layer used to synchronize the canonical 78-entry dataset, processed website export, legacy Dataset v1 downloads, and the public corpus inventory. Run:

```bash
python3 scripts/sync-corpus-bibliography.py --check
python3 scripts/export-corpus-inventory.py --check
```

to verify that those exports remain consistent.

The public corpus catalogue mirrors the 62 linked source PDFs under
`website/html/papers/corpus/`. Regenerate and verify that static mirror with:

```bash
python3 scripts/publish-corpus-papers.py
python3 scripts/publish-corpus-papers.py --check
```

`scripts/export-corpus-inventory.py` emits the corresponding `publishedPdf`
path for each of the 78 metadata entries, including entries that share a
source file. The site renders a direct download only when that checked-in copy
exists.

#### `rh_corpus_knowledge_graphs.json`
**RDF-style knowledge graph format:**
```json
{
  "@context": "https://schema.org/",
  "@graph": [
    {
      "@id": "arXiv:1211.5191",
      "@type": "ScholarlyArticle",
      "name": "Approximate Functional Equations...",
      "author": ["Bettin", "Conrey", "Farmer"],
      "mentions": ["Riemann_Zeta", "Dirichlet_L-functions"],
      "cites": [...],
      "citedBy": [...]
    }
  ]
}
```

## Using the Dataset

### Load in Python
```python
import json

# Load complete database
with open('extracted/rh_corpus_database_complete.json') as f:
    corpus = json.load(f)

# Find papers by a mathematician
papers_by_conrey = [p for p in corpus['papers'].values() 
                    if 'Conrey' in p['authors']]

# Find papers about a concept
zeta_papers = [p for p in corpus['papers'].values() 
               if 'Zeta_Function' in p['concepts']]
```

### Load in R
```r
library(jsonlite)
corpus <- fromJSON('extracted/rh_corpus_database_complete.json')
papers <- corpus$papers
```

### Query via SPARQL
```sparql
PREFIX schema: <https://schema.org/>

SELECT ?paper ?author WHERE {
  ?paper a schema:ScholarlyArticle ;
         schema:author ?author .
  FILTER (?author = "Conrey")
}
```

## Metadata Schema

### Paper Object
```json
{
  "id": "arXiv:XXXX.XXXXX",
  "title": "...",
  "authors": ["Author1", "Author2"],
  "year": 2012,
  "category": "analytic|spectral|probabilistic|functional",
  "url": "https://arxiv.org/abs/...",
  "abstract": "...",
  "key_novelties": [
    "Novelty 1: ...",
    "Novelty 2: ..."
  ],
  "formalizable_elements": [
    "Element 1: ...",
    "Element 2: ..."
  ],
  "concepts": [
    "Riemann_Zeta_Function",
    "Explicit_Formulas",
    "..."
  ],
  "intuitions": [
    "Insight 1: ...",
    "Insight 2: ..."
  ],
  "related_papers": ["arXiv:...", "arXiv:..."],
  "references": ["Titchmarsh:1951", "Montgomery:1973"]
}
```

### Mathematician Object
```json
{
  "id": "Conrey",
  "name": "Brian Conrey",
  "birth_year": 1950,
  "bio": "...",
  "papers": ["arXiv:1211.5191", "..."],
  "key_concepts": ["L-functions", "Zero Statistics", "..."],
  "contributions": ["Developed XXX", "Proved YYY"]
}
```

### Concept Object
```json
{
  "id": "Riemann_Zeta_Function",
  "name": "Riemann Zeta Function",
  "description": "...",
  "papers": ["arXiv:...", "..."],
  "related_concepts": ["Functional Equation", "Critical Strip", "..."],
  "historical_notes": "..."
}
```

## Statistics

- **Total Papers:** 78
- **Year Range:** 1859–2023 (164 years)
- **Unique Authors:** 26+
- **Categories:**
  - Analytic: 45%
  - Functional: 17%
  - Spectral: 15%
  - Probabilistic: 23%

## Access & Licensing

### License
**CC0 1.0 Universal** — Public domain dedication

You are free to:
- Copy, distribute, modify the dataset
- Use for commercial or non-commercial purposes
- No attribution required

### Citation
If you use this dataset in research:
```bibtex
@dataset{fresquet2026riemann,
  author = {Fresquet, Xavier},
  title = {The Riemann Hypothesis Corpus: 78-Entry Metadata Inventory},
  year = {2026},
  note = {CC0 1.0 Universal}
}
```

## Data Quality

**Extraction Methods:**
- Automated PDF parsing (PyPDF2, pdfplumber)
- Manual verification of key papers
- Knowledge graph construction via semantic analysis
- Cross-reference validation

**Known Limitations:**
- Some older papers available only as PDFs (OCR used)
- Intuitions extracted via LLM analysis (human review recommended)
- Some metadata may be incomplete for early papers

## Contributing Data Improvements

Found an error or want to add a paper?

1. Create issue on [GitHub](https://github.com/xavierfresquet/riemann-hypothesis/issues)
2. Include paper metadata and source
3. Propose changes to JSON structure
4. Pull requests welcome!

## Processing Scripts

See `../notebooks/` for:
- `01_corpus_ingestion.ipynb` — Loading and exploring papers
- `02_llm_insight_extraction.ipynb` — Extracting intuitions
- `03_auto_formalization_eval.ipynb` — Assessing formalizability

## Publication & Archives

This dataset is available on:
- **Zenodo** — Permanent archival with DOI
- **OSF (Open Science Framework)** — Community access
- **GitHub** — Version controlled, community contributions

---

**Last updated:** July 17, 2026  
**Papers verified:** 78/78  
**Metadata completeness:** 95%+
