# Strategy — Research Programmes and Roadmaps

Complete formalization and research plans for each phase of the project.

---

## H15: Centered Möbius–Vasyunin Quadratic Cancellation

### Documents

**1. H15_EXACT_THEOREM_SPECIFICATION.tex**
- Exact mathematical statement of the H15 problem
- Precise kernel definition
- Boundary conditions and normalization
- Target bound statement

**2. H15_RESEARCH_AGENDA.md**
- High-level decision document (2026-07-14)
- Why H15 shifted from Lean task to pure research problem
- Three proof routes explained
- Timeline and expert consultation strategy

### Status
- **Phase 0 (Freeze)**: ✅ Exact problem statement locked
- **Phase 1 (Diagnostics)**: Pending (7 decompositions to identify cancellation mechanism)
- **Phase 2–4 (Routes)**: Pending (Route 1: Estermann; Route 2: Reciprocity; Route 3: Dirichlet polynomial)
- **Fallback**: Honest conjecture + conditional theorem

### Key Insight
**H15 is a genuine open research problem.** The cancellation is global and centered; pointwise simplifications fail. Do not attempt Lean proof before understanding the mathematics.

---

## Phase NB: Nyman–Beurling / RH Bridge

### Location
See memory: `phase_nb_nyman_beurling_rh_bridge_roadmap.md`

### Summary
Replace the single axiom `nyman_beurling_criterion_iff_RH` with 7 sub-phases:

- **NB0** (1–2d): Audit and split axiom into explicit structure
- **NB1** (1–2d): Connect Báez–Duarte to Nyman–Beurling criterion
- **NB2** (3–5d): Mellin transform formulas for χ and ρ_θ
- **NB3** (5–7d): Log-pullback isometry, Mellin–Plancherel
- **NB4** (5–7d): Hardy-space point evaluation continuity
- **NB5** (3–5d): Zero-detection theorem
- **NB6** (2–3d): Convert to RH statement
- **NB7** (8+ weeks): Optional converse (defer)

### Timeline
- **Forward direction (NB0–NB6)**: ~4–8 weeks
- **Converse (NB7)**: Later (not needed for RH proof)

### Key Insight
This is **classical functional analysis with no breakthroughs needed.** All machinery exists in Mathlib or is textbook material. Slower than H14 but more straightforward.

---

## H14: Linear Möbius / Decay Estimates

### Location
See memory: `h14_honest_completion_status.md`

### Summary
**Three independent classical pieces**, NOT one:

1. **FEFactorInterpolation** (2–3 weeks)
   - Complex Gamma vertical estimate
   - Explicit `sorry` in H14FEFactorPL.lean:63
   - Routes: Stirling/Gamma, holomorphic normalization, Borel-Carathéodory direct

2. **ZetaBorelJensenFactorizationAtHeight** (3–4 weeks)
   - Height-uniform zeta factorization
   - Independent of FEFactor

3. **ZeroFreeRegionPerronApplication** (3–4 weeks)
   - Effective Perron + contour bounds
   - Independent of both above

### Timeline
- **Total**: 8–11 weeks (not 2–4)
- **Confidence**: Medium (three independent hard classical pieces)

### Key Insight
Vertical growth alone is NOT sufficient. Even after it's proved, two downstream gaps remain. All three pieces are needed.

---

## H13: Vasyunin Bridge (Complete ✅)

No active research needed. Fully proved (tag: `verified-h13-complete`, 2026-07-10).

See technical/TECHNICAL_REPORT.md for the analysis.

---

## Master Roadmap

See **doc/status/README.md** for the complete chain and timeline.

Quick summary:
```
H13 (✅) 
  ↓
H14 (🔴 60%, 8–11 weeks)
  ↓
H15 (❌ open, 3–12 months)
  ↓
Báez–Duarte Criterion
  ↓
Phase NB (🟢 mapped, 4–8 weeks)
  ↓
Riemann Hypothesis
```

---

## For Codex Prompts

Pre-written Codex prompts (in scratchpad, to be moved):
- `CODEX_H14_COMPLETION_PROMPT.md` — FEFactor interpolation (Route A/B/C options)
- (H15 will have a separate diagnostic + three-route prompt once Phase 1 diagnostics complete)

