/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.EnergyResidueReduction

/-!
# The exact BCF critical-line cancellation target

The remaining Phase 7b.1 theorem is not a pointwise upper bound for zeta.
It is cancellation in the squared numerator
`|1 - zeta(1/2 + it) * V_N(1/2 + it)|^2`, after integration and comparison
with the zero contribution.  This file exposes that target in exactly the
form used by the BCF Mellin--Plancherel identity, and proves its equivalence
with the existing energy-residue interface.

It deliberately does not prove the target.  A proof must combine the
Lemma 2 residue expansion, the Lemma 3 control of its zero-residue term, and
the contour estimates.  In particular, a pointwise subconvexity estimate for
`zeta` alone cannot establish this cancellation statement.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Lemmas 2--3 and the proof of Theorem 1.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped Topology
open Filter Topology

/-- The actual Phase 7b.1 analytic target.  This is an integrated
zeta--Dirichlet-polynomial cancellation estimate, normalized at the
logarithmic height cutoff. -/
def BCFExactCriticalLineCancellation : Prop :=
  Tendsto
    (fun N : ℕ ↦
      Real.log N *
          ((1 / (2 * Real.pi)) *
            ∫ t : ℝ,
              ‖1 - riemannZeta (criticalLine t) *
                bcfDirichletPolynomial N (criticalLine t)‖ ^ 2 /
                (1 / 4 + t ^ 2)) -
        bcfZeroWeightSumUpToHeight (Real.log N))
    atTop (𝓝 0)

/-- For each finite polynomial, the direct cancellation expression is the
critical-line residue error already isolated by the Mellin--Plancherel
development. -/
theorem bcfExactCriticalLineCancellation_error_eq (N : ℕ) :
    Real.log N *
        ((1 / (2 * Real.pi)) *
          ∫ t : ℝ,
            ‖1 - riemannZeta (criticalLine t) *
              bcfDirichletPolynomial N (criticalLine t)‖ ^ 2 /
              (1 / 4 + t ^ 2)) -
      bcfZeroWeightSumUpToHeight (Real.log N) =
    bcfCriticalLineResidueError N := by
  unfold bcfCriticalLineResidueError bcfCriticalLineIntegrand
    bcfCriticalLineNumerator
  ring

/-- The direct BCF cancellation theorem and the prior energy-residue target
are equivalent, not competing estimates. -/
theorem bcfExactCriticalLineCancellation_iff_criticalLineResidueReduction :
    BCFExactCriticalLineCancellation ↔ BCFCriticalLineResidueReduction := by
  constructor <;> intro h
  · unfold BCFExactCriticalLineCancellation at h
    unfold BCFCriticalLineResidueReduction
    refine h.congr' ?_
    filter_upwards with N
    exact bcfExactCriticalLineCancellation_error_eq N
  · unfold BCFCriticalLineResidueReduction at h
    unfold BCFExactCriticalLineCancellation
    refine h.congr' ?_
    filter_upwards with N
    exact (bcfExactCriticalLineCancellation_error_eq N).symm

/-- Once the true integrated cancellation estimate and the independently
established zero-weight formula are available, the BCF logarithmic asymptotic
follows by the already proved limit assembly. -/
theorem bcfLogAsymptotic_of_exactCriticalLineCancellation
    (hzero : BCFZeroWeightFormula)
    (hcancel : BCFExactCriticalLineCancellation) :
    BCFLogAsymptotic :=
  bcfLogAsymptotic_of_criticalLineResidueReduction hzero
    (bcfExactCriticalLineCancellation_iff_criticalLineResidueReduction.mp hcancel)

end

end NBMellinTools.H15BCF
