# H15 papers audit manifest

This manifest is the checked-in acquisition and audit record for the H15
research session. Bibliographic fields were verified against the corresponding
arXiv records on 2026-07-23. It distinguishes a paper’s relevance to a research
question from any claim that the paper proves an H15 theorem.

## Acquisition record

The original working list said “about 9” downloads but contained **10** rows
marked `NEED`, plus arXiv:1111.0931 already in the local archive. All 10 marked
sources were acquired and PDF-validated; all 11 papers below have individual
JSON-LD records in this directory.

| arXiv ID | Verified title | Authors | Audit status | H15 role |
|---|---|---|---|---|
| 2405.06349 | *On certain Gram matrices and their associated series* | Werner Ehm | pending | Nyman–Beurling Gram-matrix context |
| 1111.0931 | *Period functions and cotangent sums* | Sandro Bettin; Brian Conrey | reviewed | Cotangent-sum and reciprocity background |
| 2204.03754 | *Higher uniformity of arithmetic functions in short intervals I. All intervals* | Kaisa Matomäki; Xuancheng Shao; Terence Tao; Joni Teräväinen | pending | Low-product-row cancellation candidate |
| 1711.10582 | *A refinement of the Burgess bound for character sums* | Bryce Kerr; Igor E. Shparlinski; Kam Hung Yau | rejected | Burgess comparison; phase mismatch |
| 2002.03435 | *Burgess bounds for short character sums evaluated at forms II: the mixed case* | Lillian B. Pierce | pending | Mixed-phase comparison |
| 1502.00769 | *Trilinear forms with Kloosterman fractions* | Sandro Bettin; Vorrapan Chandee | pending | DFI-style phase-conversion candidate |
| 1111.6190 | *A Variational Barban-Davenport-Halberstam Theorem* | Allison Lewko; Mark Lewko | rejected | Additive-sieve comparison; does not control the target phase |
| 2001.05114 | *Partial Gaussian sums and the Pólya--Vinogradov inequality for primitive characters* | Matteo Bordignon | pending | Character-sum / dispersion comparison |
| 2004.10086 | *An exponentially averaged Vasyunin formula* | Sébastien Darses; Erwan Hillion | pending | Alternative Vasyunin / period-function route |
| 1509.05363 | *The Erdos discrepancy problem* | Terence Tao | pending | Bounded-phase analogue |
| math/0509480 | *Applications of the L-functions ratios conjectures* | J. B. Conrey; Nina C. Snaith | rejected | Mollified-moments comparison; conjectural route |

## Corrections to the initial working list

- arXiv:2405.06349 is Ehm’s Gram-matrix paper, not a paper titled “On Explicit
  Formulae and the Riemann Hypothesis.”
- arXiv:2204.03754 is the Matomäki–Shao–Tao–Teräväinen short-interval
  uniformity paper, not “On the Möbius function in all its glory.”
- arXiv:1111.0931 is by Bettin and Conrey (not Farmer) and concerns period
  functions and cotangent sums. The separate BCF Dirichlet-polynomial source
  in the local corpus is arXiv:1211.5191.

## Registry and website integration

Run the following from the repository root after changing a paper record:

```bash
python3 scripts/ingest-artifacts.py
python3 scripts/build-artifact-index.py --validate
python3 scripts/export-artifact-registry.py
```

The Artifact Explorer treats `auditStatus` as research metadata and displays
the role, recorded finding, bibliographic reference, and explicit `informs`
links to the H15 research gate. It does not treat an audit status as formal
verification.

The same 11 PDFs are published under `website/html/papers/h15-audit/` by
`scripts/publish-h15-audit-papers.py`, making the website’s audit cards directly
downloadable rather than metadata-only.
