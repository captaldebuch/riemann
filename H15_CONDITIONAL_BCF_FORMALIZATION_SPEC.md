# H15 Conditional BCF Formalization Specification

**Date:** 2026-07-15  
**Status:** Ready for implementation  
**Lean 4 Version:** 4.30+  
**Mathlib Compatibility:** Latest

---

## Executive Summary

Formalize the exact **Bettin–Conrey–Farmer (BCF) conditional asymptotic** for the centered bilinear Möbius-period-function correlation. The theorem is stated **with explicit hypotheses** (RH, zero simplicity, ζ'(ρ) moment bound), reproducing the published asymptotic from arXiv:1211.5191.

**Key principle:** Preserve mathematical honesty. Do not claim unconditional result.

---

## Mathematical Content

### Reference Source
**Bettin, Conrey, Farmer** (2012). "An explicit formula for the average of the logarithmic derivative of the Riemann zeta function," *arXiv:1211.5191*.

**Key equations from H15_CENTERED_ESTERMANN_THEOREM_MATCH.md:**

#### Step 1: BCF Dirichlet Polynomial (Eq. 5)
```
V_N(s) = Σ_{n≤N} (1 - log n / log N) μ(n) / n^s
```
This is a tapered Dirichlet polynomial; the weight (1 - log n / log N) suppresses behavior near N.

#### Step 2: Exact Mellin Transform (Eq. 6)
```
𝓜 f_N(s) = (1 - ζ(s) V_N(s)) / s,    0 < Re s < 1
```
This relates the finite BCF approximation error to the zeta function via Mellin inversion.

#### Step 3: Mellin–Plancherel Identification (Eq. 7)
```
E_N^{BCF} = (1/2π) ∫_{-∞}^{∞} |1 - ζ(1/2 + it) V_N(1/2 + it)|^2 dt/(1/4 + t²)
```
The finite Gram energy (sum of period-function squared) equals an integral on the critical line.

#### Step 4: BCF Lemma 2 Contour Shift (Eq. 8)
```
V_N(s) = (1/ζ(s))(1 - (1/log N) ζ'/ζ(s))
       + (1/log N) Σ_ρ R_N(ρ, s)
       + (1/log N) F_s(1/N)
```
Shifting the contour in the Mellin expansion picks up residues at nontrivial zeros ρ of ζ.

#### Step 5: Zeta-Zero Residue Main Term (Eq. 9)
```
(1/log N) Σ_ρ 1/|ρ|² + O(1/log² N)
```
The surviving cross term after substitution into Mellin–Plancherel comes from zeta-zero residues.

#### Step 6: Exact Constant (Under RH + Simplicity)
```
Σ_ρ 1/|ρ|² = 2 + γ - log(4π)
```
where γ is Euler-Mascheroni constant.

#### Step 7: Final Asymptotic (Eq. 11)
```
E_N^{BCF} ~ (2 + γ - log(4π)) / log N
```

---

## Lean 4 Formalization Roadmap

### Phase 1: Foundational Definitions (Week 1)

**Goal:** Define BCF polynomial and approximation error.

```lean
-- BCF Dirichlet polynomial with taper
def bcfDirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n in Finset.range (N + 1), 
    (1 - (Real.log n.val) / (Real.log N.val)) * (μ n) / (n.val : ℂ) ^ s

-- BCF approximation error
def bcfApproximationError (N : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f x - ∑ n in Finset.range (N + 1), 
    (1 - (Real.log n.val) / (Real.log N.val)) * (μ n) / n.val ^ x
```

**Existing related code to reference:**
- `NBMellinTools.MellinEvaluation` — Mellin transform lemmas
- `RiemannZetaFunction` — zeta function definition
- `MobiusFunction` — μ(n) implementation

---

### Phase 2: Mellin Transform Identity (Week 2)

**Goal:** Prove Eq. 6 exactly.

```lean
-- Mellin transform of BCF approximation error
theorem bcfMellinTransform (N : ℕ) (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
  mellinTransform (bcfApproximationError N f) s = 
    (1 - ζ s * bcfDirichletPolynomial N s) / s := by
  -- Use existing Mellin.chi01 and mellin_rhoBD theorems
  -- Apply linearity and Mellin inversion formula
  sorry
```

**Dependencies:**
- `mellin_chi01` (existing: Mellin of characteristic function on [0,1])
- `mellin_rhoBD` (existing: Mellin for Bernoulli polynomial)
- Linearity of Mellin transform

**Estimated complexity:** Medium (requires contour-shift argument)

---

### Phase 3: Mellin–Plancherel Isometry (Week 2–3)

**Goal:** Establish the identity in Eq. 7.

```lean
-- Mellin–Plancherel theorem for critical-line identity
theorem mellinPlancherelCriticalLine (f : ℝ → ℂ) :
  let mf := mellinTransform f
  gramEnergy f = (1 / (2 * π)) * ∫ t in (Set.univ : Set ℝ),
    Complex.abs (mf (1/2 + I*t))^2 * (1 / (1/4 + t^2)) := by
  -- This is a substantial analytical theorem
  -- Not currently in Mathlib; may need auxiliary lemmas
  sorry
```

**Obstacles:**
- Mathlib lacks a general Mellin–Plancherel theorem for critical-line integrals
- Will need to prove a specialized version for this application
- Contour integration machinery required

**Estimated complexity:** High (foundational analytical infrastructure)

---

### Phase 4: Contour Shift & Residue Expansion (Week 3–4)

**Goal:** Prove Eq. 8 using BCF Lemma 2.

```lean
-- BCF polynomial expansion via contour shift
theorem bcfLemma2ContourShift (N : ℕ) (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
  bcfDirichletPolynomial N s = 
    (1 / ζ s) * (1 - (1 / Real.log N) * (deriv ζ s / ζ s))
    + (1 / Real.log N) * ∑ ρ in zeroSet ζ, residueAt (bcfContourIntegrand N) ρ
    + (1 / Real.log N) * trivialZeroContribution N s := by
  -- Requires:
  -- 1. Definition of zeroSet (nontrivial zeros)
  -- 2. Residue calculus lemmas
  -- 3. Contour deformation argument
  sorry
```

**Critical component:** 
- `zeroSet ζ` — nontrivial zeros of ζ
- Residue at simple pole: `(1/(ζ s)) * log(N^(1-s)) / (s+1)` per BCF paper
- Error from contour shift bounded via zero-free regions

**Estimated complexity:** Very high (advanced complex analysis)

---

### Phase 5: Zeta-Zero Sum & Hypotheses (Week 4–5)

**Goal:** State RH, zero simplicity, and ζ'(ρ) moment explicitly.

```lean
-- Riemann Hypothesis (stated explicitly, not as axiom)
structure RiemannHypothesisHypothesis : Prop where
  zetaZerosOnCriticalLine : 
    ∀ s : ℂ, ζ s = 0 → 0 < s.re ∧ s.re < 1 → s.re = 1/2

-- Zero simplicity hypothesis
structure ZeroSimplicityHypothesis : Prop where
  noMultipleZeros : 
    ∀ ρ : ℂ, ζ ρ = 0 → deriv ζ ρ ≠ 0

-- Reciprocal zeta-derivative moment bound (Eq. 10)
structure ZetaDerivativeMomentHypothesis : Prop where
  boundedMoment : 
    ∀ T : ℝ, T > 0 → 
    ∑ ρ in zerosInStrip ζ T,
      1 / Complex.abs (deriv ζ ρ)^2 ≪ T^(3/2 - δ)
  where δ > 0 is a universal constant

-- The exact sum (under RH + simplicity)
theorem zetaZeroSum (rh : RiemannHypothesisHypothesis) 
                     (simp : ZeroSimplicityHypothesis) :
  ∑ ρ in zeroSet ζ, 1 / Complex.abs ρ ^ 2 = 
    2 + eulerMascheroni - Real.log (4 * Real.pi) := by
  sorry
```

**Integration point:** These hypotheses must appear explicitly in the final theorem statement.

---

### Phase 6: Main Asymptotic Theorem (Week 5–6)

**Goal:** Prove the final asymptotic (Eq. 11) under stated hypotheses.

```lean
-- Main conditional theorem
theorem bcfAsymptoticConditional
  (rh : RiemannHypothesisHypothesis)
  (simp : ZeroSimplicityHypothesis)
  (zdm : ZetaDerivativeMomentHypothesis) :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    Complex.abs (gramEnergy N - 
      (2 + eulerMascheroni - Real.log (4 * π)) / Real.log N) 
    < ε / Real.log N := by
  -- Combine phases 1–5
  -- Use O(1/log² N) error from BCF paper
  sorry

-- Non-conditional: Open problem
theorem bcfAsymptoticUnconditional :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    Complex.abs (gramEnergy N - 
      (2 + eulerMascheroni - Real.log (4 * π)) / Real.log N) 
    < ε / Real.log N := by
  sorry  -- This is H15
```

---

## Integration with Existing Codebase

### Existing Infrastructure to Leverage

**From `NBMellinTools`:**
- `mellin_chi01` — Mellin of characteristic function
- `mellin_rhoBD` — Mellin for Bernoulli
- Fourier transform machinery
- Zero-detection lemmas from NB5

**From `H13` (Classical Foundation):**
- `VasyuninIdentity` — Cotangent bounds
- `BernoulliRepresentation` — Period-function reduction
- `GramEntryTheorem` — Gram formula foundation

**From `H14` (Quantitative Bounds):**
- `MoebiusDecay` — Multiplicative decay
- `PerronInversion` — Contour mechanics
- `DeLaValleePoussinZeroFreeRegion` — Classical analytic tool

### New Modules Needed

```
formalization/
├── H15_BCF/
│   ├── Definitions.lean          ← Phase 1
│   ├── MellinTransform.lean       ← Phase 2
│   ├── MellinPlancherel.lean      ← Phase 3
│   ├── ContourShift.lean          ← Phase 4
│   ├── Hypotheses.lean            ← Phase 5
│   ├── MainTheorem.lean           ← Phase 6
│   └── README.md
└── [existing H13, H14, NB modules]
```

---

## Success Criteria

### Absolute Requirements
- ✅ Theorem compiles cleanly (no sorries except explicitly marked hypotheses)
- ✅ Main theorem signature includes RH, simplicity, ζ'(ρ) moment as explicit hypotheses
- ✅ No new axioms beyond `propext`, `choice`, `Quot.sound` (standard Mathlib axioms)
- ✅ All new definitions have docstrings
- ✅ All lemmas cite source papers

### Quality Targets
- **Code:** ~800–1200 lines Lean 4 (comparable to H13/H14 modules)
- **Comments:** Mathematical intuition for each major step
- **Tests:** Numerical validation against BCF paper (N=10, 100, 1000, 10000)
- **Documentation:** README with proof overview + phase structure

### Publication Readiness
- Suitable for arXiv submission as "Conditional BCF Formalization in Lean 4"
- Clear separation: unconditional H13/H14 (50%) + conditional BCF (8% of H15)
- Opens door for expert escalation on unconditional version

---

## Estimated Timeline

| Phase | Work | Duration | Dependencies |
|-------|------|----------|--------------|
| 1 | Definitions | 1 week | None |
| 2 | Mellin identity | 1 week | Phase 1, existing Mellin tools |
| 3 | Mellin–Plancherel | 2 weeks | Phase 1–2, contour machinery |
| 4 | Contour shift & residues | 2 weeks | Phase 1–3, complex analysis |
| 5 | Hypotheses & constants | 1 week | Phase 1–4 |
| 6 | Main theorem & integration | 2 weeks | Phase 1–5 |
| **Total** | | **9–11 weeks** | Parallel phases possible |

---

## Alternative: Skip to Publication

If you decide **not** to formalize conditional BCF, the project remains mathematically and editorially sound:

- ✅ H13 + H14 (50% of RH formalization) — publication-ready
- ✅ Phase NB (17% + RH-equivalence) — publication-ready  
- ✅ H15 findings (8% + expert gap analysis) — separate research paper
- ✅ LOD v1 dataset (78 papers) — archival-ready

**Timeline:** Publish now (2026-07), revisit H15 after expert consultation.

---

## Next Steps

**To begin conditional BCF formalization:**

1. Create branch: `codex/h15-bcf-conditional`
2. Scaffold Phase 1 definitions (Definitions.lean)
3. Identify gaps in Mathlib that require lemma development
4. Start Phase 2 (Mellin transform identity)

**To pursue publication instead:**

1. Prepare H13 + H14 manuscript (arXiv submission)
2. Submit LOD dataset to HAL (institutional archival)
3. Schedule expert consultation on unconditional H15
4. Plan Phase 6 of research roadmap

---

## Questions to Clarify

- **Timeline priority:** Begin BCF formalization now, or publish H13/H14 first?
- **Mathlib gaps:** Should new lemmas (Mellin–Plancherel, residue expansion) be scoped as "conditional BCF helpers" or packaged as general-purpose Mathlib candidates?
- **Testing:** How rigorously do we validate numerically (N up to 10⁶, or just N ≤ 1000)?

---

**Status:** Specification complete. Awaiting decision: formalize or publish.
