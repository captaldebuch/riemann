# Literature — Classical Sources for RH via Nyman–Beurling

All papers referenced in the formalization project.

## Core Papers

### 1. Bettin & Conrey (2013) — Period Functions and Cotangent Sums
**File**: `1111.0931v2.pdf`  
**Title**: Approximations to the Riemann Hypothesis  
**arXiv**: 1111.0931v2  
**Role**: H15 kernel machinery (period functions, cotangent reciprocity, quantum modular forms)  
**Key sections**:
- Theorem 1: Period function functional equation
- Vasyunin cotangent formula: V(h/k) = ...
- Bettin–Conrey reciprocity: xV(x) + V(1/x) − 1/(πDen(x)) = g(x)

**Status**: Reviewed. Contains reciprocity machinery but NOT the uniform Möbius–sawtooth bound.

---

### 2. Auli, Bayad, Beck (2017) — Reciprocity Relations
**File**: `1601.06839v3.pdf`  
**Title**: Reciprocal Relations and *-Type Theorems  
**arXiv**: 1601.06839v3  
**Role**: H15 reciprocity structure  
**Key sections**:
- Theorem 1.1: Reciprocity for cotangent sums (with gcd structure)
- Theorem 1.2: Integral representation (note: assumes Re(a) > 1, not Re(a) > −1)

**Status**: Reviewed. Provides reciprocity but assumes Re(a) > 1 (stricter than stated in some references).

---

### 3. Bettin, Conrey, Farmer (2012) — Nyman-Beurling and RH
**File**: `1211.5191v1.pdf`  
**Title**: Explicit Formula for the Asymptotic Variance of the Riemann Zeta  
**arXiv**: 1211.5191v1  
**Role**: Nyman-Beurling criterion via explicit formulas  

⚠️ **CRITICAL ISSUE**: This paper **ASSUMES RH** in its main theorem. Cannot be used unconditionally to derive RH.

**Status**: Reviewed. Machinery is valid but circular for our purposes.

---

### 4. Montgomery & Vaughan (2007) — Multiplicative Number Theory
**File**: `9780521849036_frontmatter.pdf`  
**Title**: Multiplicative Number Theory I: Classical Theory  
**Publisher**: Cambridge University Press  
**Role**: Mellin transforms, Estermann zeta, contour shifting, zero-free regions  
**Chapters cited**:
- Chapter 5: Mellin transforms (claimed in some references; verify against actual text)
- Chapter 13: Contour shifting, Perron's formula (claimed in some references; verify against actual text)

**Status**: Partial. Only frontmatter (17 pages) available; missing main chapters.

---

## Papers in the Archive

Some additional papers are in `.archive/` (not here):

- `papers/baez_balazard_landreau_saias_2003_autocorrelation.pdf` — Estermann zeta (Props 50–66)
- `papers/burnol_2002_balazard_saias_estimate.pdf` — Saias bounds

These are referenced for H14/H15 machinery but not essential for the basic route.

---

## How to Use This Folder

1. **Before starting H15 research**: Read Bettin-Conrey (1111.0931v2) for the period-function and reciprocity framework.

2. **For H15 diagnostics**: Reference Auli-Bayad-Beck (1601.06839v3) for the reciprocity structure.

3. **For Nyman-Beurling bridge (Phase NB)**: Bettin-Conrey-Farmer (1211.5191v1) has the machinery, but note the RH assumption.

4. **For contour analysis**: Montgomery-Vaughan chapter references (if complete text is obtained).

---

## What's Missing (and Why)

- ✅ Bettin & Conrey (2013) — Main H15 reference, complete
- ❌ Bettin, Conrey, Farmer (2012) — Has circular RH dependency
- ⚠️ Montgomery & Vaughan (2007) — Only frontmatter; chapters 5, 13 missing
- ❌ Baez–Duarte et al. — In `.archive/` (Estermann, autocorrelation reference)

---

## Notes for Researchers

- All PDFs are local. For updates or access, use arXiv IDs to fetch latest versions.
- Some papers assume standard definitions (e.g., Bettin convention for cotangent vs. other sources).
- Montgomery-Vaughan is the standard reference for Mellin/Perron/contour shifting, but only frontmatter is here. Obtain full text for chapters 5, 13 if working on H14 contour analysis.

