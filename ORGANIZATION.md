# Project Organization Guide

## Folder Structure

### `proofs/`
**Lean 4 formal verification source code**

```
proofs/
├── NBMellinTools/           # Main library (NB = Nyman-Beurling)
│   ├── LogPullback.lean     # Mellin transform foundations
│   ├── MellinEvaluation.lean # Exact formulas
│   ├── BaezDuarteTail.lean  # BBLS theoretical framework
│   └── H15BCF/              # Phase 7b work
│       ├── Definitions.lean
│       ├── Asymptotic.lean
│       ├── MultiplicityZeroCounting.lean
│       ├── GenusOneProduct.lean
│       ├── GenusOneWeierstrass.lean
│       ├── GenusOneMajorantReduction.lean
│       ├── HeightTruncationProduct.lean
│       └── FinalAnalyticAssembly.lean
└── README.md                # Build instructions
```

**To build:**
```bash
cd proofs
lake build NBMellinTools
```

**Key facts:**
- Zero new axioms (only Lean.Prelude + Mathlib foundations)
- Zero `sorry` statements
- Verified by `mathlib/verify.sh`

---

### `dataset/`
**Riemann Hypothesis corpus and extracted knowledge**

```
dataset/
├── corpus/                  # 63 local PDF files; 62 linked by the 78-entry metadata inventory
│   ├── analytic/           # Classical analysis papers
│   ├── spectral/           # Spectral/Hilbert-Pólya
│   ├── probabilistic/      # Random matrices, GUE
│   └── functional/         # Nyman-Beurling, harmonic analysis
├── extracted/              # Processed metadata
│   ├── rh_corpus_database_complete.json
│   ├── rh_corpus_knowledge_graphs.json
│   └── rh_intuitions_extracted.json
└── README.md               # Dataset documentation
```

**Metadata includes:**
- Author information (26 key mathematicians)
- Concepts and keywords (260+ mathematical concepts)
- Intuitions (400+ extracted insights)
- Related papers (citation network)
- Formalizable elements (what can go into Lean)

**License:** CC0 1.0 Universal (public domain)

---

### `website/`
**Interactive web interface**

```
website/
├── html/                    # Static HTML pages
│   ├── index.html          # Home page
│   ├── css/                # Styling
│   ├── js/
│   │   ├── app.js          # SPA router
│   │   ├── data.js         # Corpus data embedded
│   │   └── sparql-client.js # LOD query client
│   └── downloads/          # Proof archives
├── lean/                    # LOCAL COPIES of proof files
│   ├── H15BCF/             # All Phase 7b proofs
│   │   ├── FinalAnalyticAssembly.lean
│   │   ├── GenusOneMajorantReduction.lean
│   │   └── ...
│   └── view-proof.html     # Proof viewer (syntax highlighted)
├── localhost.py            # Simple dev server
└── README.md               # Deployment instructions
```

**Pages:**
- **Home** — Overview, current efforts, milestones
- **Corpus & Dataset** — 78 metadata entries, search, and source-status labels
- **Intuitions & Strategies** — Historical timeline, mathematician profiles
- **Current Efforts** — H13, H14, Phase NB, H15 status
- **Technical Reports** — 2-page scientific papers on each phase
- **Knowledge Explorer** — Interactive maps of concepts and papers

**To run locally:**
```bash
cd website
python3 localhost.py
# Visit http://localhost:8000
```

---

### `reports/`
**Technical papers and progress documents**

```
reports/
├── H13-H14-Classical-Routes.html        # Technical report
├── Phase-NB-Functional-Analysis.html    # Technical report
├── H15-BCF-Asymptotic.html              # Technical report
├── Phase-7b-Progress.md                 # Current status
└── README.md                            # How to read reports
```

Each technical report includes:
- Mathematical definitions and theorems
- Proof sketches
- Lean formalization details
- Links to source code

---

### `notebooks/`
**Jupyter analysis and exploration**

```
notebooks/
├── 01_corpus_ingestion.ipynb           # Load and explore papers
├── 02_llm_insight_extraction.ipynb     # Extract mathematical intuitions
├── 03_auto_formalization_eval.ipynb    # Assess formalizability
└── README.md                           # Setup instructions
```

**Dependencies:**
```bash
cd notebooks
pip install jupyter pandas matplotlib requests
jupyter notebook
```

---

### `.worktrees/`
**Git feature branches (development)**

```
.worktrees/
├── h15-bcf-conditional/                # Active H15 Phase 7b branch
│   └── mathlib/NBMellinTools/H15BCF/   # Live proof development
└── [other archived branches]
```

**Note:** `.worktrees/` is used during development. Merged branches move to `.archive/`.

---

### `.archive/`
**Completed branches and obsolete work**

```
.archive/
├── verified-h13-complete/
├── verified-h14-complete/
├── verified-phase-nb-complete/
└── [other completed milestones]
```

---

## Publishing Separate Components

### 1. **Riemann Dataset**
```bash
tar -czf riemann-dataset.tar.gz dataset/ notebooks/README.md
# Contents: 78 metadata entries + linked PDF archive + JSON metadata + license
```

**For publication to:**
- Zenodo (with DOI)
- OSF (Open Science Framework)
- GitHub release

---

### 2. **Riemann Proofs**
```bash
tar -czf riemann-proofs.tar.gz proofs/ lakefile.toml lean-toolchain BUILD.md
# Contents: Lean source + build config + verification scripts
```

**For publication to:**
- GitHub (main repo)
- Zenodo
- ACM DL (if submitting paper)

---

### 3. **Riemann Website**
```bash
# Deploy to static hosting
cd website/html
# Option A: GitHub Pages
#   git subtree push --prefix website/html origin gh-pages
# Option B: Netlify
#   (drag & drop website/html folder)
# Option C: Local server (for demos)
#   cd website && python3 localhost.py
```

---

### 4. **Riemann Reports**
```bash
tar -czf riemann-reports.tar.gz reports/
# Contents: Technical papers (H13, H14, Phase NB, H15, Phase 7b progress)
```

**For publication to:**
- arXiv (as preprints)
- GitHub releases
- Project website

---

## File Copying & Linking Strategy

### Lean Files for Website Viewing
```bash
# Copy latest proofs to website for local viewing
cp -r .worktrees/h15-bcf-conditional/mathlib/NBMellinTools/H15BCF/* website/lean/H15BCF/

# Keep in sync when developing:
# (Add to .git/hooks/post-commit if needed)
```

### Website Links Format
```html
<!-- Link to local Lean file -->
<a href="./lean/H15BCF/GenusOneMajorantReduction.lean" target="_blank">
  View source
</a>

<!-- Link to deployed proof on GitHub -->
<a href="https://github.com/xavierfresquet/riemann-hypothesis/blob/main/proofs/NBMellinTools/H15BCF/GenusOneMajorantReduction.lean" target="_blank">
  View on GitHub
</a>
```

---

## Cleanup & Maintenance

### Files to Delete/Archive
```bash
# Scratch work and test scripts
rm -rf scratch/ *.py [test files]

# Move to archive if keeping for reference
mv experimental-attempts/ .archive/

# Remove duplicate corpus JSONs
# Keep only: rh_corpus_database_complete.json
```

### Regular Maintenance
1. **After each commit:** Sync `website/lean/` with `proofs/`
2. **Before publication:** Run full verification suite
3. **Monthly:** Update README and progress documents

---

## Quick Commands

```bash
# Build and verify
lake build NBMellinTools
mathlib/verify.sh

# Check axioms (should show only Lean/Mathlib foundations)
grep -r "axiom\|sorry" proofs/

# Run website locally
cd website && python3 localhost.py

# Prepare dataset for publication
tar -czf riemann-dataset.tar.gz dataset/

# Check all links in website
python3 link_checker.py website/html/

# Archive a completed branch
git worktree remove --force .worktrees/[branch]
mv .git/worktrees/[branch] .archive/
```

---

## Version Control Strategy

**Main branch:** Stable, published code
```bash
git commit -m "feat(h15): [component] — [what changed]"
```

**Feature branches (via `.worktrees/`):**
```bash
git worktree add .worktrees/feature-name origin/feature-name
# Develop in worktree...
# Merge back to main when complete
git checkout main
git merge feature-name
git worktree remove .worktrees/feature-name
```

---

## Documentation to Update Regularly

1. **[README.md](README.md)** — Overall status and links
2. **[BUILD.md](BUILD.md)** — Build instructions (in proofs/)
3. **[reports/Phase-7b-Progress.md](reports/)** — Current research status
4. **[website/README.md](website/)** — Deployment guide

---

**Last updated:** July 17, 2026
