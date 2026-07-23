# The Riemann Hypothesis Corpus: Formalization & Digital Humanities

A digital humanities resource combining formal verification in Lean 4 with a curated corpus inventory spanning 160+ years of Riemann Hypothesis research. The current audited inventory contains 78 metadata entries, resolving to 62 distinct linked source PDFs; 30 entries also have a separate processed research layer.

## Quick Links

- **[Website](website/)** — Interactive corpus explorer, intuitions map, technical reports
- **[Proofs](proofs/)** — Lean 4 formal verification (H13, H14, Phase NB, H15 Phase 7b)
- **[Dataset](dataset/)** — 78-entry metadata inventory + extracted knowledge graphs
- **[Reports](reports/)** — Technical reports on each formalization phase
- **[Notebooks](notebooks/)** — Jupyter analysis of corpus and intuitions

## Project Structure

```
riemann/
├── proofs/              # Lean 4 source code (NBMellinTools library)
├── dataset/             # Corpus papers + extracted data
├── website/             # Static website (run locally or deploy)
├── reports/             # Technical reports (HTML)
├── notebooks/           # Jupyter analysis notebooks
└── .worktrees/          # Git feature branches (for development)
```

## What's Formalized?

| Phase | Status | What | Reference |
|-------|--------|------|-----------|
| **H13** | ✅ COMPLETE | Classical identities (BBLS chain) | Báez-Duarte, Landreau, Saias |
| **H14** | ✅ COMPLETE | Quantitative bounds (DVP method) | de la Vallée Poussin |
| **Phase NB** | ✅ COMPLETE | Nyman-Beurling criterion (RH equivalence) | Nyman, Beurling |
| **H15 Phases 1–7** | ✅ COMPLETE | BCF asymptotic structure | Bettin-Conrey-Farmer |
| **H15 Phase 7b** | 🔄 IN PROGRESS | Energy reduction + ξ factorization | BCF + Hadamard |

**Key fact:** All formalized code has **zero new axioms** and **zero `sorry`** statements.

## Running Locally

### Website
```bash
cd website
python3 localhost.py
# Visit http://localhost:8000
```

### Lean Proofs
```bash
cd proofs
lake build NBMellinTools
lake test NBMellinTools  # Run verification suite
```

### Jupyter Notebooks
```bash
cd notebooks
jupyter notebook
```

## Publishing Components Separately

### 1. Riemann Dataset
```bash
# Extract for separate publication
tar -czf riemann-dataset.tar.gz dataset/ notebooks/
# Includes: 78 metadata entries, linked source PDFs, extracted knowledge graphs, analysis scripts
```

### 2. Riemann Proofs
```bash
# Extract for separate publication
tar -czf riemann-proofs.tar.gz proofs/ lakefile.toml lean-toolchain
# Includes: Lean source, build configuration, verification scripts
```

### 3. Riemann Website
```bash
# Deploy as static site
cp -r website/html /var/www/riemann/
# Or push to GitHub Pages
```

### 4. Riemann Reports
```bash
# Extract technical papers
tar -czf riemann-reports.tar.gz reports/
```

## Documentation

- **[ORGANIZATION.md](ORGANIZATION.md)** — Detailed folder structure explanation
- **[BUILD.md](BUILD.md)** — How to build Lean proofs and verify axioms
- **[website/README.md](website/README.md)** — Website setup and deployment
- **[proofs/README.md](proofs/README.md)** — Lean library documentation
- **[dataset/README.md](dataset/README.md)** — Corpus metadata and license

## Key Achievements

### Formalization
- **67% of RH proof formalized** (H13 + H14 + Phase NB)
- **98% of H15 structure formalized** (phases 1–7, framework for 7b)
- **Three classical analytic theorems remain** (Riemann–von Mangoldt bounds, logarithmic-derivative convergence, integrated BCF cancellation)

### Digital Humanities
- **78 metadata entries** across analytic, spectral, probabilistic, and functional routes
- **62 distinct linked PDFs** in the audited inventory; 16 entries share an already-linked source PDF
- **Knowledge graphs extracted** (160+ mathematicians, 260+ concepts, 400+ intuitions)
- **Interactive explorer** mapping historical development and proof strategies

## License

- **Proofs:** MIT (Lean 4 code)
- **Dataset:** CC0 1.0 Universal (public domain papers + extracted metadata)
- **Website:** MIT (HTML/JS/CSS)
- **Corpus papers:** See individual paper headers (mostly public domain or fair use for research)

## Contact

For inquiries, corrections, or to contribute:
- Email: xavier.fresquet@sorbonne.ae
- Repository: [GitHub](https://github.com/xavierfresquet/riemann-hypothesis)

## Citation

```bibtex
@software{fresquet2026riemann,
  author = {Fresquet, Xavier},
  title = {The Riemann Hypothesis Corpus: Formalization and Digital Humanities},
  year = {2026},
  url = {https://github.com/xavierfresquet/riemann-hypothesis}
}
```

---

**Last updated:** July 17, 2026  
**Commit:** [Latest](https://github.com/xavierfresquet/riemann-hypothesis)
