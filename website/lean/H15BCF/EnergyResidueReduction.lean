/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.Asymptotic

/-!
# BCF critical-line energy-to-residue reduction

This is the concrete Phase 7b.1 analytic target. The unconditional
Mellin--Plancherel theorem rewrites the remaining energy-residue reduction as
a statement about one explicit critical-line integral. Therefore future kernel
decay and contour estimates can target `bcfCriticalLineResidueError` directly.

No decay estimate is asserted here: proving the displayed limit remains the
analytic work that must use the Phase 6 contour identity and its bounds.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped Topology
open Filter Topology

/-- The normalized difference between the exact critical-line energy integral
and the height-truncated zero-weight term. -/
def bcfCriticalLineResidueError (N : ℕ) : ℝ :=
  (Real.log N / (2 * Real.pi)) *
      (∫ t : ℝ, bcfCriticalLineIntegrand N t) -
    bcfZeroWeightSumUpToHeight (Real.log N)

/-- The explicit critical-line form of the remaining Phase 7b.1 analytic
estimate. -/
def BCFCriticalLineResidueReduction : Prop :=
  Tendsto bcfCriticalLineResidueError atTop (𝓝 0)

/-- Mellin--Plancherel identifies the abstract normalized energy-residue error
with the explicit critical-line integral error, for every finite `N`. -/
theorem bcfEnergyResidueError_eq_criticalLineResidueError (N : ℕ) :
    Real.log N * bcfGramEnergy N -
        bcfZeroWeightSumUpToHeight (Real.log N) =
      bcfCriticalLineResidueError N := by
  rw [bcfGramEnergy_eq_criticalLineEnergy]
  unfold bcfCriticalLineEnergy bcfCriticalLineResidueError
  ring

/-- The original Phase 6-to-7 energy-residue reduction is equivalent to the
explicit critical-line integral estimate. -/
theorem bcfEnergyResidueReduction_iff_criticalLine :
    BCFEnergyResidueReduction ↔ BCFCriticalLineResidueReduction := by
  constructor
  · intro h
    refine h.congr' ?_
    filter_upwards with N
    exact bcfEnergyResidueError_eq_criticalLineResidueError N
  · intro h
    refine h.congr' ?_
    filter_upwards with N
    exact (bcfEnergyResidueError_eq_criticalLineResidueError N).symm

/-- The explicit Phase 7b.1 critical-line estimate, together with the
separate zero-weight formula, completes the formal Phase 6-to-7 implication. -/
theorem bcfLogAsymptotic_of_criticalLineResidueReduction
    (hzero : BCFZeroWeightFormula) (hcritical : BCFCriticalLineResidueReduction) :
    BCFLogAsymptotic :=
  bcfLogAsymptotic_of_energyResidueReduction hzero
    (bcfEnergyResidueReduction_iff_criticalLine.mpr hcritical)

/-- The original BCF proof targets the normalized energy asymptotic directly.
Once that asymptotic and the independent zero-weight formula are known, the
critical-line residue-reduction statement follows by limit algebra.  Thus this
proposition is a useful contour-analysis interface, but not a replacement for
the cancellation estimate in BCF's proof of Theorem 1. -/
theorem bcfCriticalLineResidueReduction_of_bcfLogAsymptotic
    (hlog : BCFLogAsymptotic) (hzero : BCFZeroWeightFormula) :
    BCFCriticalLineResidueReduction := by
  unfold BCFCriticalLineResidueReduction
  have hzero_log := hzero.tendsto_along_logNat
  unfold BCFLogAsymptotic at hlog
  have hdiff :
      Tendsto
        (fun N : ℕ ↦
          Real.log N * bcfGramEnergy N -
            bcfZeroWeightSumUpToHeight (Real.log N))
        atTop (𝓝 0) := by
    simpa using hlog.sub hzero_log
  refine hdiff.congr' ?_
  filter_upwards with N
  exact bcfEnergyResidueError_eq_criticalLineResidueError N

end

end NBMellinTools.H15BCF
