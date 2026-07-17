/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.Hypotheses

/-!
# Conditional BCF final-asymptotic interface

This file gives the exact, formally checkable Phase 7 target and proves its
elementary equivalence with the normalized logarithmic limit. It deliberately
does **not** assert that limit: deriving it requires the still-open contour
witness, residue estimates, and the classical zero-weight formula.

The point of this interface is to prevent a later analytic proof from losing a
factor of `log N` when passing from the normalized limit to the published BCF
error formulation.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped Topology
open Filter Topology

/-- The normalized form of the BCF final asymptotic. -/
def BCFLogAsymptotic : Prop :=
  Tendsto (fun N : ℕ ↦ Real.log N * bcfGramEnergy N) atTop
    (𝓝 bcfAsymptoticConstant)

/-- The normalized error whose convergence to zero is equivalent to
`BCFLogAsymptotic`. -/
def bcfNormalizedError (N : ℕ) : ℝ :=
  Real.log N * bcfGramEnergy N - bcfAsymptoticConstant

/-- The remaining analytic bridge from the Phase 6 residue expansion to the
Phase 7 energy limit.  Its proof must use the constructed contour witness,
residue estimates, and Mellin--Plancherel; it is deliberately an explicit
proposition rather than an axiom or an asserted theorem. -/
def BCFEnergyResidueReduction : Prop :=
  Tendsto
    (fun N : ℕ ↦
      Real.log N * bcfGramEnergy N -
        bcfZeroWeightSumUpToHeight (Real.log N))
    atTop (𝓝 0)

/-- The classical zero-weight limit composed with the logarithmic height
cutoff. -/
theorem BCFZeroWeightFormula.tendsto_along_logNat
    (h : BCFZeroWeightFormula) :
    Tendsto (fun N : ℕ ↦ bcfZeroWeightSumUpToHeight (Real.log N)) atTop
      (𝓝 bcfAsymptoticConstant) := by
  exact h.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Phase 6 to Phase 7 limit assembly.**  Once the contour/residue analysis
has supplied the explicit energy-residue reduction, the zero-weight formula
gives the normalized BCF final asymptotic by limit algebra. -/
theorem bcfLogAsymptotic_of_energyResidueReduction
    (hzero : BCFZeroWeightFormula) (henergy : BCFEnergyResidueReduction) :
    BCFLogAsymptotic := by
  unfold BCFEnergyResidueReduction at henergy
  unfold BCFLogAsymptotic
  have hzero_log := hzero.tendsto_along_logNat
  convert henergy.add hzero_log using 1 <;> ring_nf

/-- The normalized BCF limit is equivalent to convergence of the normalized
error to zero. -/
theorem bcfLogAsymptotic_iff_tendsto_normalizedError :
    BCFLogAsymptotic ↔ Tendsto bcfNormalizedError atTop (𝓝 0) := by
  constructor
  · intro h
    simpa [BCFLogAsymptotic, bcfNormalizedError] using
      h.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ bcfAsymptoticConstant) atTop (𝓝 bcfAsymptoticConstant))
  · intro h
    simpa [BCFLogAsymptotic, bcfNormalizedError] using
      h.add (tendsto_const_nhds :
        Tendsto (fun _ : ℕ ↦ bcfAsymptoticConstant) atTop (𝓝 bcfAsymptoticConstant))

/-- A normalized BCF limit makes its normalized error eventually smaller than
any positive tolerance. -/
theorem BCFLogAsymptotic.eventually_abs_normalizedError_lt
    (h : BCFLogAsymptotic) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |bcfNormalizedError N| < ε := by
  have hzero : Tendsto bcfNormalizedError atTop (𝓝 0) :=
    bcfLogAsymptotic_iff_tendsto_normalizedError.mp h
  filter_upwards [hzero.eventually (Metric.ball_mem_nhds 0 hε)] with N hN
  simpa [Metric.mem_ball, Real.dist_eq] using hN

/-- The exact epsilon formulation of the BCF final asymptotic. -/
def BCFPublishedAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |bcfGramEnergy N - bcfAsymptoticConstant / Real.log N| <
      ε / Real.log N

/-- The normalized logarithmic limit implies the published BCF asymptotic
form, with the denominator controlled explicitly from `N ≥ 2`. -/
theorem BCFLogAsymptotic.published
    (h : BCFLogAsymptotic) : BCFPublishedAsymptotic := by
  intro ε hε
  have h_eventual :
      ∀ᶠ N : ℕ in atTop,
        |bcfGramEnergy N - bcfAsymptoticConstant / Real.log N| <
          ε / Real.log N := by
    filter_upwards [h.eventually_abs_normalizedError_lt hε,
      (eventually_ge_atTop 2 : ∀ᶠ N : ℕ in atTop, 2 ≤ N)] with N hnorm hN
    have h_one_lt : (1 : ℝ) < N := by
      exact_mod_cast lt_of_lt_of_le one_lt_two hN
    have hlog : 0 < Real.log N := Real.log_pos h_one_lt
    have hidentity :
        Real.log N *
            (bcfGramEnergy N - bcfAsymptoticConstant / Real.log N) =
          bcfNormalizedError N := by
      unfold bcfNormalizedError
      field_simp [hlog.ne']
    rw [lt_div_iff₀ hlog]
    calc
      |bcfGramEnergy N - bcfAsymptoticConstant / Real.log N| * Real.log N =
          |Real.log N *
            (bcfGramEnergy N - bcfAsymptoticConstant / Real.log N)| := by
              rw [abs_mul, abs_of_pos hlog]
              ring
      _ = |bcfNormalizedError N| := congrArg abs hidentity
      _ < ε := hnorm
  rcases (eventually_atTop.1 h_eventual) with ⟨N₀, hN₀⟩
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

end

end NBMellinTools.H15BCF
