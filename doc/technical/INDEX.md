# Technical Analysis — Detailed Reports and Specifications

Deep-dive analysis of the formalization and mathematics.

---

## TECHNICAL_REPORT.md

**Content**: Detailed breakdown of what's in the Lean code

**Sections**:
- Current state (definitions, theorems, axioms)
- Known issues (definitions as stubs, axiom mismatches)
- Paper reference audit (which claimed theorems are actually in the papers)
- What would be needed to complete (if attempted via formalization alone)

**Status**: Complete as of 2026-07-14

**Use case**: Understanding the gap between what the Lean code claims and what's actually proved. Reference before starting any Lean work.

---

## Audit Reports (In Memory, Future)

When complete, H14 and H15 analyses will be added here:

- `H14_COMPLETION_AUDIT.md` — Three independent pieces, not one
- `H15_FORMULATION_ERROR_AUDIT.md` — Why sawtooth proxy is false
- `H15_CANCELLATION_ATLAS.ipynb` — 7 diagnostic decompositions (once run)

---

## Mathematical Background

For deeper understanding of the classical machinery:

- **Mellin transforms** — Log-pullback, Plancherel on half-line, point evaluation
- **Estermann zeta** — Definition, poles, functional equation, vertical growth (BBLS)
- **Nyman–Beurling criterion** — Hilbert space setup, generator setup, Mellin formulation
- **Zero-free regions** — De la Vallée Poussin (1899), effective Perron, contour shifting

These are in classical references (Montgomery-Vaughan, BBLS papers). This folder documents how they apply to the RH formalization.

---

## TeX Specifications

Additional formal specifications (separate from code):

- `H15_EXACT_THEOREM_SPECIFICATION.tex` (moved to strategy/) — Mathematical statement of H15

---

## Formalization Readiness

Once the mathematical pieces are solved:

- **H14**: Formalize Stirling/Gamma (FEFactor), then Jensen, then Perron
- **H15**: Formalize the proof route (whichever closes first)
- **Phase NB**: Formalize Mellin machinery, then zero-detection, then RH conversion

This folder tracks the gap between "mathematics is understood" and "Lean proof is ready."

