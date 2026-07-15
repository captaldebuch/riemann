# H15 New Research Angles: Analysis of Expanded Corpus
**Date:** 2026-07-15  
**Trigger:** 27 new papers added; H15-classified papers now include alternative techniques

> **Source-audit update:** Angle 1 is no longer the recommended proof route.
> ArXiv `1409.1634` was misidentified in the corpus, `1601.06839` contains
> Estermann/cotangent reciprocity rather than character bounds, and the exact
> character expansion leaves a Mobius-twisted character sum plus non-unit
> strata. See `H15_CHARACTER_SUM_ROUTE_AUDIT.md` for the derivation and revised
> ranking.

---

## Current H15 Status Recap

**Blocked Route:** Direct analytic approach via DFI/Bettin–Chandee (bound 8× too weak)

**Missing Piece:** Unconditionally, a centered asymptotic strong enough to
imply RH. The exact Estermann insertion has now been checked, and the
published BCF main term is known to arise from zeta-zero residues under RH
and a reciprocal zeta-derivative moment hypothesis. See
`H15_CENTERED_ESTERMANN_THEOREM_MATCH.md`.

**Decision:** Research-only (not formalized). But with expanded corpus, three NEW angles emerge.

---

## Angle 1: Character Sum Diagnostic (AUDITED)

### Hypothesis
The unit-residue part of the Möbius/period-function correlation admits an
exact weighted Dirichlet-character expansion. The audit asks what remains
after that finite rewrite; it does not assume classical bounds close H15.

### Papers and source corrections
- **0804.0645:** Beck--Halloran, *Finite Trigonometric Character Sums Via
  Discrete Fourier Analysis* -- supports exact finite character identities,
  not the required varying-modulus bound.
- **1601.06839:** Auli--Bayad--Beck, *Reciprocity Theorems for Bettin--Conrey
  Sums* -- supports the Estermann route, not a character-bound route.
- **1409.1634:** Bourgain--Demeter, *Decouplings for curves and hypersurfaces
  with nonzero Gaussian curvature* -- unrelated to the proposed character
  reduction and misidentified in the corpus.

### Key Insight
For `(b,q)=1`, multiplicative Fourier inversion expresses `beta_q(b)` using
only odd nonprincipal characters. After the additive H15 phase is inserted,
Gauss sums leave a varying-modulus, Mobius-twisted character sum. Non-unit
residues require additional quotient-modulus strata. This is a precise
diagnostic, not automatic cancellation.

### Technical Route
1. **Factorization via characters:** restrict `beta_q` to `(b,q)=1` and take
   its multiplicative Fourier transform.
2. **Orthogonality relations:** Use $\sum_\chi \chi(a)\overline{\chi(b)} = \phi(q) \cdot \mathbb{1}_{a \equiv b \pmod q}$ to isolate modular contributions
3. **Character sum audit:** identify the resulting Mobius-twisted sums and
   non-unit strata explicitly.
4. **Decision gate:** do not claim `O(1/log N)` unless the complete centered
   main term and the varying-modulus remainder are both controlled.

### Audited outcome
- Characters diagonalize the unit stratum exactly.
- They do not avoid Estermann machinery for the complete H15 phase.
- Classical untwisted character bounds do not control the resulting
  Mobius-twisted partial sums.
- Character-wise absolute bounds do not generate the centered main term.

### Lean Feasibility
Finite orthogonality is **high feasibility**, but the needed analytic bounds
are **low feasibility** in the current library. Mathlib contains character
orthogonality but no identified Polya--Vinogradov or Burgess theorem here.
No H15 Lean work should begin from this angle.

---

## Angle 2: Automorphic Forms / GL(2) Route (SOURCE-BLOCKED)

### Hypothesis
The cotangent/Estermann object inside the Gram kernel may encode spectral
properties of a GL(2) Eisenstein series. This is an identification problem,
not yet a theorem about the raw Nyman generator.

### Source audit
- **1503.05121** is *An averaged form of Chowla's conjecture* by
  Matomaki--Radziwill--Tao, not *Fourier Analysis on GL(2)*.
- **1807.08249** is an astrophysics habilitation on weak cosmological
  lensing, not *L-Functions and Modular Forms*.

These records cannot support the proposed GL(2) route. A replacement primary
source with an exact theorem for the centered BCF object has not been
identified.

### Key Insight
Automorphic forms on GL(2) are exactly the objects that encode:
- Modular structure (via the underlying lattice)
- Functional equations (via the Mellin transform)
- Character theory (via Hecke eigenvalues)

The Bettin--Conrey period function has an Eisenstein-series origin. It has not
been shown here that the raw Nyman generator $x\mapsto\{1/x\}$ is itself an
automorphic coefficient with the required BCF truncation and centering.

### Technical Route
1. **Identification gate:** exhibit an exact automorphic object whose
   coefficient is the complete centered BCF kernel, including its truncation.
2. **Spectral decomposition:** Write $F = \sum_\phi c_\phi \phi$ where $\phi$ ranges over automorphic spectrum
3. **Cancellation test:** determine exactly which cross terms are removed by
   Petersson orthogonality and which weighted remainder survives.
4. **Bound via L-function growth:** Apply bounds on $L(1/2 + it, \pi)$ to control the cancellation rate

### Why This Might Work
- Automorphic forms encode modular structure and functional equations.
- Eisenstein-series expansions may identify the missing diagonal or polar
  contribution.
- Spectral orthogonality is useful only after the exact centered BCF object and
  its coefficients have been identified.

### Lean Feasibility
⚠️ **MEDIUM** — Automorphic forms exist in some Mathlib/research formalization, but GL(2) machinery is sparse. Requires careful porting.

---

## Angle 3: Kuznetsov Trace Formula / Spectral Method (AUDITED)

### Hypothesis
Use a Kuznetsov/Estermann trace or reciprocity formula directly at the
spectral level, with the diagonal or polar main term retained. Estimating only
the L² norm of $\beta_q$ has already been shown insufficient.

### Papers checked
- **1111.0931:** gives exact cotangent/period-function reciprocity, but its
  reciprocal companion does not match the symmetric BCF pair after the
  modular-inverse substitution.
- **1601.06839:** gives Bettin--Conrey sum reciprocity and Estermann special
  values, not a Kuznetsov theorem.
- **1411.7764:** gives mean-square results for zeta times finite Dirichlet
  polynomials in specified length regimes; its ideal trilinear estimate is
  conjectural and would imply Lindelof.

### Key Insight
The Kuznetsov trace formula is:
$$\sum_{\text{automorphic}} \lambda_\pi(n) \lambda_\pi(m) = \delta_{n,m} + \text{(oscillating terms)}$$

The diagonal term, not merely spectral norm cancellation, is the prospective
source of the scalar and logarithmic terms needed by the centered BCF energy.
The off-diagonal must then be estimated only after summing the exact Mobius
logarithmic weights.

### Technical Route
1. **Exact insertion:** place the primitive Estermann spectrum into the full
   centered BCF identity without taking componentwise absolute values.
2. **Trace/reciprocity formula:** identify the diagonal or polar main term.
3. **Main-term matching:** prove that this term cancels the explicit scalar
   and log-ratio contributions with the required residual constant.
4. **Off-diagonal estimate:** control the total weighted remainder at
   `o(1/log N)` or better.

### Audited outcome
The exact insertion is equation (3) of
`H15_CENTERED_ESTERMANN_THEOREM_MATCH.md`. The `1/2` in the primitive
Estermann spectrum has zero real contribution, so it does not itself produce
the scalar/logarithmic centering. The verified BCF main term instead comes
from residues at zeta zeros after Mellin--Plancherel and contour shifting.

### Why This Might Work
- It preserves the main term that generic norm estimates discard.
- A trace formula separates diagonal and off-diagonal contributions exactly.
- It matches the Estermann spectrum already proved for `beta_q`; success is
  still contingent on a sufficiently strong weighted remainder theorem.

### Lean Feasibility
⚠️ **LOW-MEDIUM** — Trace formulas are advanced; spectral theory formalization is sparse. But worth exploring conceptually.

---

## Angle 4: Conditional Routes / Numerical Validation

### Hypothesis
Since we've proven the exact centered-bilinear kernel and the DFI/Bettin–Chandee gap, perhaps we can:

1. **Prove the O(1/log N) bound conditionally** (assuming some reasonable conjecture on amplitudes)
2. **Verify numerically to 5+ decimal places** that the bound holds for N up to 10⁶

This creates a **strong empirical foundation** for expert escalation and might guide the proof strategy.

### Papers to Investigate
- **2607.09110:** "Phase 1 Diagnostics for H15 Kernel" (new, 2026) — might contain numerical validation
- **2607.09797:** "Recent Advances in RH Approximations" (new, 2026) — might have computational insights
- **2607.04632:** "Möbius Correlations and Cancellation" (new, 2026) — might show empirical cancellation

### Technical Route
1. **Conditional formulation:** use a correctly normalized aggregate
   assumption. The pointwise claim $|\beta_q(b)|\le B/\sqrt q$ is incompatible
   with the known prime second moment; only `beta_q(b)/q` has RMS scale
   `q^(-1/2)`.
2. **Compute the actual implication:** retain the centered identity and test
   whether the stated aggregate hypothesis is sufficient; do not infer the
   target from a pointwise RMS-scale guess.
3. **Numerical validation:** For N = 10, 100, 1000, 10000, compute actual cancellation vs. theoretical bound
4. **Report findings:** If empirics match theory, highlight which assumption(s) are tight

### Why This Might Work
- Experts are often guided by empirical evidence
- A precisely stated conditional theorem plus reproducible numerics can be a
  useful research artifact if it is clearly separated from an unconditional
  result.
- Guides future proof work (shows exactly where tightness lies)

### Lean Feasibility
Numerical feasibility is **high outside Lean**. Numerical evidence is not a
formal theorem, and an `N=10^6` computation should not be presented as a Lean
proof of an asymptotic statement.

---

## Proposed Research Agenda (4–8 weeks)

| Week | Angle | Action | Deliverable |
|------|-------|--------|-------------|
| **1** | **Angle 1 (Chars)** | Source audit + exact unit-stratum transform | Completed diagnostic factorization |
| **2** | **Angle 1 (Chars)** | Trace non-unit and Mobius-twisted remainders | Completed obstruction audit |
| **3** | **Angle 2 (Auto)** | Study 1503.05121 + 1807.08249 | Automorphic form identification (if exists) |
| **4** | **Angle 2 (Auto)** | Sketch GL(2) spectral orthogonality argument | Plausibility assessment |
| **5** | **Angle 3 (Spectral)** | Literature review: trace formulas in modern form | Applicable formula(s) identified |
| **6** | **Angle 4 (Conditional)** | Conditional formulation + numerical validation | Empirical report (N up to 10⁶) |
| **7** | **Synthesis** | Compare all four angles; identify most promising | Revised H15 strategy memo |
| **8** | **Documentation** | Write research findings; prepare expert brief | Publication-ready research note |

---

## Success Criteria

✅ **Minimal:** One of the four angles yields a **proof sketch** with clear remaining gaps  
✅ **Strong:** Two angles converge on the **same mechanism** (suggests deep truth)  
✅ **Exceptional:** Full O(1/log N) proof via any angle  

---

## Why This Timing Is Good

1. **Corpus expanded:** 27 new papers provide fresh perspectives
2. **H15 gap identified:** We know EXACTLY what's missing (Estermann/Kuznetsov)
3. **Three newly catalogued H15 papers (2026):** Their metadata and theorem
   relevance still require source validation.
4. **Character and automorphic literature:** Mathematically developed, but
   the analytic bounds and GL(2) machinery needed here are not present in the
   checked Mathlib package.
5. **Project status:** 67% complete — can afford 4–8 week exploratory investment

---

## Risk Assessment

| Angle | Risk | Mitigation |
|-------|------|-----------|
| **Chars** | Untwisted bounds miss the Mobius weight and centered main term | Retain only as a diagnostic unless a sufficient varying-modulus theorem is found |
| **Auto** | GL(2) machinery not in Mathlib | Focus on conceptual sketch, not formalization |
| **Spectral** | Trace formulas might not simplify the problem | Start with literature review to assess |
| **Conditional** | Empirical validation is not a proof | Position as "research foundation" not solution |

---

## Recommendation

**Use the published conditional BCF mechanism as the next theorem package.**
Keep the character and Estermann formulae as exact diagnostics. The next
formalizable slice is the algebraic Mellin identity for the BCF polynomial,
followed by Mellin--Plancherel; RH and the reciprocal `zeta'` moment must be
explicit hypotheses of the asymptotic. Do not relabel the missing
unconditional estimate as a classical trace-formula consequence.

---

**Status:** CHARACTER AND CENTERED ESTERMANN ROUTES AUDITED; CONDITIONAL BCF
MECHANISM IDENTIFIED; UNCONDITIONAL H15 REMAINS OPEN
