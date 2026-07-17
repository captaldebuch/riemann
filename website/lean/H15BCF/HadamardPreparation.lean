/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.Analytic.Order
import NBMellinTools.H15BCF.ZeroWeightFormula

/-!
# Completed xi and multiplicity-aware zero weights

This file supplies the formal objects needed by the classical
Hadamard-product calculation of the BCF leading constant.  It does not assert
a canonical product: Mathlib does not yet contain the required entire-function
factorization or its logarithmic differentiation.

The important distinction is that a canonical product counts zeros with their
analytic multiplicities, while the simple-zero BCF contour expansion uses a
finite set of distinct zeros.  The multiplicity-weighted sum defined here is
therefore the mathematically correct input to the product calculation.  Under
the separate zero-simplicity hypothesis, a later local-order theorem will
identify it with the existing distinct-zero sum.

We use the entire pole-removed `completedRiemannZeta₀` to define xi:

`xi(s) = (s * (s - 1) * completedRiemannZeta₀(s) + 1) / 2`.

Away from `0` and `1`, this is the usual
`s * (s - 1) * completedRiemannZeta(s) / 2`; the displayed formulation is
entire in Mathlib without assigning artificial values at the two poles.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, introduction and Lemma 2.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The entire Riemann xi function, expressed through Mathlib's pole-removed
completed zeta function. -/
def bcfXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- Xi is entire. -/
theorem differentiable_bcfXi : Differentiable ℂ bcfXi := by
  unfold bcfXi
  exact (((differentiable_id.mul
    (differentiable_id.sub (differentiable_const (c := (1 : ℂ))))).mul
    differentiable_completedZeta₀).add
      (differentiable_const (c := (1 : ℂ)))).div_const
        (2 : ℂ)

/-- The xi functional equation follows directly from the completed-zeta
functional equation. -/
theorem bcfXi_one_sub (s : ℂ) : bcfXi (1 - s) = bcfXi s := by
  unfold bcfXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Away from the two polar points, the entire definition agrees with the
usual product of the completed zeta function by `s * (s - 1) / 2`. -/
theorem bcfXi_eq_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    bcfXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [bcfXi, completedRiemannZeta_eq]
  field_simp [hs0, sub_ne_zero.mpr (Ne.symm hs1)]
  ring

/-- A nontrivial zeta zero is a zero of xi. -/
theorem bcfXi_zero_of_mem_bcfZerosUpToHeight
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ bcfZerosUpToHeight T) :
    bcfXi rho = 0 := by
  rw [mem_bcfZerosUpToHeight] at hrho
  have hrho_ne_zero : rho ≠ 0 := by
    intro hzero
    have hre := hrho.2.1
    rw [hzero] at hre
    norm_num at hre
  have hrho_ne_one : rho ≠ 1 := by
    intro hone
    have hre := hrho.2.2.1
    rw [hone] at hre
    norm_num at hre
  rw [bcfXi_eq_completedRiemannZeta hrho_ne_zero hrho_ne_one,
    completedRiemannZeta_zero_of_mem_bcfZerosUpToHeight (by
      rw [mem_bcfZerosUpToHeight]
      exact hrho)]
  ring

/-- The analytic multiplicity of a zero of xi.  This is the multiplicity
which occurs in the classical Hadamard product. -/
def bcfXiZeroMultiplicity (rho : ℂ) : ℕ :=
  analyticOrderNatAt bcfXi rho

/-- The local expression for xi obtained by replacing completed zeta with
zeta and the inverse archimedean gamma factor.  It is only used in a
neighborhood of a nontrivial zero, where its denominator is nonzero. -/
private def bcfXiZetaFactor (s : ℂ) : ℂ :=
  (s * (s - 1) * riemannZeta s) / (2 * (Gammaℝ s)⁻¹)

/-- At a simple nontrivial zero of zeta, the analytic order of xi is one.
This is the precise local bridge between the multiplicities in a canonical
product and the existing `ZeroSimplicityHypothesis`. -/
theorem ZeroSimplicityHypothesis.xiMultiplicity_one
    (hsimple : ZeroSimplicityHypothesis) {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    bcfXiZeroMultiplicity rho = 1 := by
  rw [mem_bcfZerosUpToHeight] at hrho
  have hrho_ne_zero : rho ≠ 0 := by
    intro hzero
    have hre := hrho.2.1
    rw [hzero] at hre
    norm_num at hre
  have hrho_ne_one : rho ≠ 1 := by
    intro hone
    have hre := hrho.2.2.1
    rw [hone] at hre
    norm_num at hre
  have hgamma : Gammaℝ rho ≠ 0 := Gammaℝ_ne_zero_of_re_pos hrho.2.1
  have hgamma_inv : (Gammaℝ rho)⁻¹ ≠ 0 := inv_ne_zero hgamma
  have hlocal : bcfXi =ᶠ[𝓝 rho] bcfXiZetaFactor := by
    filter_upwards [eventually_ne_nhds hrho_ne_zero,
      eventually_ne_nhds hrho_ne_one,
      (differentiable_Gammaℝ_inv.differentiableAt.continuousAt.ne_iff_eventually_ne
        continuousAt_const).mp hgamma_inv] with z hz0 hz1 hzinv
    have hzgamma : Gammaℝ z ≠ 0 := by
      intro hzero
      apply hzinv
      simp [hzero]
    rw [bcfXi_eq_completedRiemannZeta hz0 hz1]
    unfold bcfXiZetaFactor
    rw [riemannZeta_def_of_ne_zero hz0]
    field_simp [hzgamma]
  have hderiv_zeta : HasDerivAt riemannZeta (deriv riemannZeta rho) rho :=
    (differentiableAt_riemannZeta hrho_ne_one).hasDerivAt
  have hderiv_num :
      HasDerivAt (fun z : ℂ ↦ z * (z - 1) * riemannZeta z)
        (rho * (rho - 1) * deriv riemannZeta rho) rho := by
    convert ((hasDerivAt_id rho).mul ((hasDerivAt_id rho).sub_const 1)).mul hderiv_zeta using 1
    simp [hrho.1]
  have hderiv_den :
      HasDerivAt (fun z : ℂ ↦ 2 * (Gammaℝ z)⁻¹)
        (deriv (fun z : ℂ ↦ 2 * (Gammaℝ z)⁻¹) rho) rho :=
    (((differentiable_const (c := (2 : ℂ))).mul
      differentiable_Gammaℝ_inv).differentiableAt).hasDerivAt
  have hden_ne_zero : 2 * (Gammaℝ rho)⁻¹ ≠ 0 :=
    mul_ne_zero two_ne_zero hgamma_inv
  have hderiv_factor :
      HasDerivAt bcfXiZetaFactor
        (rho * (rho - 1) * deriv riemannZeta rho / (2 * (Gammaℝ rho)⁻¹)) rho := by
    unfold bcfXiZetaFactor
    convert hderiv_num.div hderiv_den hden_ne_zero using 1
    rw [hrho.1]
    field_simp [hgamma_inv]
    ring
  have hderiv_xi : deriv bcfXi rho ≠ 0 := by
    rw [hlocal.deriv_eq, hderiv_factor.deriv]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hrho_ne_zero (sub_ne_zero.mpr hrho_ne_one))
        (hsimple.deriv_ne_zero (by
          rw [mem_bcfZerosUpToHeight]
          exact hrho)))
      hden_ne_zero
  have hxi_zero : bcfXi rho = 0 :=
    bcfXi_zero_of_mem_bcfZerosUpToHeight (by
      rw [mem_bcfZerosUpToHeight]
      exact hrho)
  have hxi_analytic : AnalyticAt ℂ bcfXi rho :=
    differentiable_bcfXi.analyticAt rho
  have horder : analyticOrderAt bcfXi rho = 1 :=
    hxi_analytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hxi_zero hderiv_xi
  simp [bcfXiZeroMultiplicity, analyticOrderNatAt, horder]

/-- The finite, multiplicity-weighted zero sum which a Hadamard/logarithmic
derivative calculation must evaluate. -/
def bcfMultiplicityZeroWeightSumUpToHeight (T : ℝ) : ℝ :=
  ∑ rho ∈ bcfZerosUpToHeight T,
    bcfXiZeroMultiplicity rho / ‖rho‖ ^ 2

/-- Every finite multiplicity-weighted zero sum is nonnegative. -/
theorem bcfMultiplicityZeroWeightSumUpToHeight_nonneg (T : ℝ) :
    0 ≤ bcfMultiplicityZeroWeightSumUpToHeight T := by
  unfold bcfMultiplicityZeroWeightSumUpToHeight
  positivity

/-- The exact multiplicity-weighted classical formula supplied by the missing
Hadamard product calculation.  Under RH, its summands are
`m(rho) / |rho|²`; without RH the product naturally yields the complex weight
`m(rho) / (rho * (1-rho))` instead.

This is a named analytic target, not a theorem or a hidden hypothesis. -/
def BCFMultiplicityZeroWeightFormula : Prop :=
  Tendsto bcfMultiplicityZeroWeightSumUpToHeight atTop
    (𝓝 bcfAsymptoticConstant)

/-- The local analytic statement needed to transfer a multiplicity-weighted
product formula to the current distinct-zero BCF sum.  It remains separate
from the global product calculation, while the required local comparison of
xi with zeta and the gamma factor is proved below. -/
def BCFXiMultiplicityOneAtNontrivialZeros : Prop :=
  ∀ rho : ℂ, rho ∈ bcfNontrivialZetaZeros → bcfXiZeroMultiplicity rho = 1

/-- Existing zeta simplicity supplies the local xi multiplicity statement
needed by the canonical-product route. -/
theorem ZeroSimplicityHypothesis.xiMultiplicityOneAtNontrivialZeros
    (hsimple : ZeroSimplicityHypothesis) :
    BCFXiMultiplicityOneAtNontrivialZeros := by
  intro rho hrho
  have hrho_height : rho ∈ bcfZerosUpToHeight ‖rho.im‖ := by
    rw [mem_bcfNontrivialZetaZeros] at hrho
    rw [mem_bcfZerosUpToHeight]
    exact ⟨hrho.1, hrho.2.1, hrho.2.2, le_rfl⟩
  exact hsimple.xiMultiplicity_one hrho_height

/-- If local simplicity has been transported to xi, then the
multiplicity-weighted and distinct-zero finite sums agree exactly. -/
theorem bcfMultiplicityZeroWeightSum_eq_distinct_of_multiplicity_one
    (hmult : BCFXiMultiplicityOneAtNontrivialZeros) (T : ℝ) :
    bcfMultiplicityZeroWeightSumUpToHeight T = bcfZeroWeightSumUpToHeight T := by
  unfold bcfMultiplicityZeroWeightSumUpToHeight bcfZeroWeightSumUpToHeight
  apply Finset.sum_congr rfl
  intro rho hrho
  have hnontrivial : rho ∈ bcfNontrivialZetaZeros := by
    rw [mem_bcfZerosUpToHeight] at hrho
    rw [mem_bcfNontrivialZetaZeros]
    exact ⟨hrho.1, hrho.2.1, hrho.2.2.1⟩
  rw [hmult rho hnontrivial]
  norm_num

/-- The multiplicity-weighted Hadamard formula plus the proved finite
comparison gives the existing distinct-zero formula used by Phase 7b.3. -/
theorem bcfZeroWeightFormula_of_multiplicity_formula
    (hmult : BCFXiMultiplicityOneAtNontrivialZeros)
    (hformula : BCFMultiplicityZeroWeightFormula) :
    BCFZeroWeightFormula := by
  unfold BCFZeroWeightFormula
  refine hformula.congr' ?_
  filter_upwards with T
  exact bcfMultiplicityZeroWeightSum_eq_distinct_of_multiplicity_one hmult T

/-- The established local xi/zeta multiplicity comparison removes the
distinct-versus-multiplicity ambiguity from the Hadamard route under the
project's existing explicit zero-simplicity hypothesis. -/
theorem bcfZeroWeightFormula_of_multiplicity_formula_of_simplicity
    (hsimple : ZeroSimplicityHypothesis)
    (hformula : BCFMultiplicityZeroWeightFormula) :
    BCFZeroWeightFormula :=
  bcfZeroWeightFormula_of_multiplicity_formula
    hsimple.xiMultiplicityOneAtNontrivialZeros hformula

end

end NBMellinTools.H15BCF
