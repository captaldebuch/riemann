/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LogDeriv
import NBMellinTools.H15BCF.HadamardTarget

/-!
# Endpoint form of the xi Hadamard calculation

The canonical product for the completed xi function naturally compares its
logarithmic derivatives at `0` and `1`.  This file proves all finite algebra
needed to identify that endpoint difference with the BCF zero weights.

The remaining classical analysis has two genuinely distinct parts:

* a canonical-product theorem and justified logarithmic differentiation,
  represented by `BCFHadamardEndpointFormula`; and
* the special-value calculation of the xi logarithmic derivative at zero,
  represented by `BCFXiLogDerivAtZeroFormula`.

Their conjunction implies the pre-existing direct Hadamard target, and hence
the distinct-zero BCF formula under RH and simplicity.  Neither statement is
assumed or proved here.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, introduction; see also the standard Hadamard
product for the Riemann xi function.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The xi function translated to the symmetry center of its functional
equation. -/
def bcfXiCentered (z : ℂ) : ℂ :=
  bcfXi ((1 / 2 : ℂ) + z)

/-- The centered xi function is even.  This is the normalization that removes
the linear term in the centered canonical-product viewpoint. -/
theorem bcfXiCentered_neg (z : ℂ) :
    bcfXiCentered (-z) = bcfXiCentered z := by
  unfold bcfXiCentered
  have harg : (1 : ℂ) - ((1 / 2 : ℂ) + z) = (1 / 2 : ℂ) + -z := by
    ring
  rw [← harg]
  exact bcfXi_one_sub ((1 / 2 : ℂ) + z)

/-- The derivative of centered xi vanishes at its symmetry center. -/
theorem deriv_bcfXiCentered_zero : deriv bcfXiCentered 0 = 0 := by
  have hfun : (fun z : ℂ ↦ bcfXiCentered (-z)) = bcfXiCentered := by
    funext z
    exact bcfXiCentered_neg z
  have hderiv := congrFun (congrArg deriv hfun) 0
  rw [deriv_comp_neg] at hderiv
  norm_num at hderiv
  linear_combination (-1 / 2 : ℂ) * hderiv

/-- Xi takes the usual value `1 / 2` at zero in the pole-removed
normalization used by Mathlib. -/
theorem bcfXi_zero : bcfXi 0 = (1 / 2 : ℂ) := by
  norm_num [bcfXi]

/-- The functional-equation partner of the preceding xi value. -/
theorem bcfXi_one : bcfXi 1 = (1 / 2 : ℂ) := by
  norm_num [bcfXi]

theorem bcfXi_zero_ne_zero : bcfXi 0 ≠ 0 := by
  rw [bcfXi_zero]
  norm_num

theorem bcfXi_one_ne_zero : bcfXi 1 ≠ 0 := by
  rw [bcfXi_one]
  norm_num

/-- Differentiating the xi functional equation relates the two endpoint
derivatives. -/
theorem deriv_bcfXi_one_eq_neg_deriv_bcfXi_zero :
    deriv bcfXi 1 = -deriv bcfXi 0 := by
  have hfun : (fun z : ℂ ↦ bcfXi (1 - z)) = bcfXi := by
    funext z
    exact bcfXi_one_sub z
  have hderiv := congrFun (congrArg deriv hfun) 0
  rw [deriv_comp_const_sub] at hderiv
  norm_num at hderiv
  linear_combination -hderiv

/-- The xi functional equation gives the endpoint relation for logarithmic
derivatives, since xi is nonzero at both endpoints. -/
theorem logDeriv_bcfXi_one_eq_neg_logDeriv_bcfXi_zero :
    logDeriv bcfXi 1 = -logDeriv bcfXi 0 := by
  simp only [logDeriv_apply]
  rw [deriv_bcfXi_one_eq_neg_deriv_bcfXi_zero, bcfXi_one, bcfXi_zero]
  ring

/-- The difference of the endpoint logarithmic derivatives is the centered
form `-2 * xi'(0) / xi(0)`. -/
theorem bcfXi_logDeriv_endpointDifference :
    logDeriv bcfXi 1 - logDeriv bcfXi 0 = -2 * logDeriv bcfXi 0 := by
  rw [logDeriv_bcfXi_one_eq_neg_logDeriv_bcfXi_zero]
  ring

/-- A nontrivial BCF zero cannot equal zero. -/
theorem bcfZero_ne_zero {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) : rho ≠ 0 := by
  rw [mem_bcfZerosUpToHeight] at hrho
  intro hzero
  rw [hzero] at hrho
  norm_num at hrho

/-- A nontrivial BCF zero cannot equal one. -/
theorem bcfZero_ne_one {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) : rho ≠ 1 := by
  rw [mem_bcfZerosUpToHeight] at hrho
  intro hone
  rw [hone] at hrho
  norm_num at hrho

/-- The individual summand obtained by subtracting the endpoint
logarithmic-derivative kernels. -/
def bcfHadamardEndpointTerm (rho : ℂ) : ℂ :=
  (bcfXiZeroMultiplicity rho : ℂ) * ((1 - rho)⁻¹ + rho⁻¹)

/-- The finite endpoint sum corresponding to a height-truncated canonical
product. -/
def bcfHadamardEndpointSumUpToHeight (T : ℝ) : ℂ :=
  ∑ rho ∈ bcfZerosUpToHeight T, bcfHadamardEndpointTerm rho

/-- The difference of the two endpoint kernels is the BCF Hadamard weight.
This is finite algebra; no product convergence or zero-density estimate is
used. -/
theorem bcfHadamardEndpointTerm_eq_zeroWeightTerm
    {rho : ℂ} (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) :
    bcfHadamardEndpointTerm rho = bcfHadamardZeroWeightTerm rho := by
  unfold bcfHadamardEndpointTerm bcfHadamardZeroWeightTerm
  have hsub : 1 - rho ≠ 0 := sub_ne_zero.mpr (Ne.symm hrho1)
  field_simp [hrho0, hsub]
  ring

/-- Every finite endpoint sum equals the finite complex zero-weight sum. -/
theorem bcfHadamardEndpointSum_eq_zeroWeightSum (T : ℝ) :
    bcfHadamardEndpointSumUpToHeight T =
      bcfHadamardZeroWeightSumUpToHeight T := by
  unfold bcfHadamardEndpointSumUpToHeight bcfHadamardZeroWeightSumUpToHeight
  apply Finset.sum_congr rfl
  intro rho hrho
  exact bcfHadamardEndpointTerm_eq_zeroWeightTerm
    (bcfZero_ne_zero hrho) (bcfZero_ne_one hrho)

/-- The completed-xi canonical-product target in its natural endpoint form.
The value is the difference of its logarithmic derivatives at `1` and `0`,
which the xi functional equation reduces to `-2 * logDeriv xi 0`. -/
def BCFHadamardEndpointFormula : Prop :=
  Tendsto bcfHadamardEndpointSumUpToHeight atTop
    (𝓝 (-2 * logDeriv bcfXi 0))

/-- The special-value part of the classical xi calculation.  Its proof
requires the gamma-factor expansion at zero; it is separate from the
canonical-product convergence theorem. -/
def BCFXiLogDerivAtZeroFormula : Prop :=
  -2 * logDeriv bcfXi 0 = (bcfAsymptoticConstant : ℂ)

/-- The endpoint product formula and the special-value calculation imply the
existing direct Hadamard zero-weight target. -/
theorem bcfHadamardLogDerivativeFormula_of_endpoint
    (hendpoint : BCFHadamardEndpointFormula)
    (hspecial : BCFXiLogDerivAtZeroFormula) :
    BCFHadamardLogDerivativeFormula := by
  unfold BCFHadamardEndpointFormula at hendpoint
  unfold BCFXiLogDerivAtZeroFormula at hspecial
  unfold BCFHadamardLogDerivativeFormula
  have hlimit :
      Tendsto bcfHadamardEndpointSumUpToHeight atTop
        (𝓝 (bcfAsymptoticConstant : ℂ)) := by
    rw [← hspecial]
    exact hendpoint
  refine hlimit.congr' ?_
  filter_upwards with T
  exact bcfHadamardEndpointSum_eq_zeroWeightSum T

/-- With the previously proved RH and zero-simplicity reductions, the two
classical endpoint inputs suffice for the distinct-zero BCF formula used in
the final energy assembly. -/
theorem bcfZeroWeightFormula_of_endpoint_of_simplicity
    (hRH : RiemannHypothesisHypothesis)
    (hsimple : ZeroSimplicityHypothesis)
    (hendpoint : BCFHadamardEndpointFormula)
    (hspecial : BCFXiLogDerivAtZeroFormula) :
    BCFZeroWeightFormula :=
  bcfZeroWeightFormula_of_hadamard_of_simplicity hRH hsimple
    (bcfHadamardLogDerivativeFormula_of_endpoint hendpoint hspecial)

end

end NBMellinTools.H15BCF
