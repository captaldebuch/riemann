/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.XiSpecialValue

/-!
# Finite canonical products for the BCF xi endpoint formula

This file formalizes the finite algebra of the canonical-product route to the
BCF zero-weight constant.  The finite product has one factor
`(1 - s / rho) ^ m(rho)` for every distinct nontrivial zero in a height
truncation.  Its endpoint logarithmic-derivative difference is exactly the
finite BCF Hadamard endpoint sum.

The remaining analytic theorem is now sharply delimited: construct and
identify the infinite (genus-one) canonical product for `bcfXi`, justify its
logarithmic differentiation, and compare its height truncations with the
finite products below.  No such convergence or factorization is asserted in
this file.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The functional equation of xi preserves analytic zero multiplicities. -/
theorem bcfXiZeroMultiplicity_one_sub (rho : ℂ) :
    bcfXiZeroMultiplicity (1 - rho) = bcfXiZeroMultiplicity rho := by
  unfold bcfXiZeroMultiplicity analyticOrderNatAt
  apply congrArg ENat.toNat
  let g : ℂ → ℂ := fun z ↦ 1 - z
  have hg : AnalyticAt ℂ g (1 - rho) := by
    dsimp [g]
    fun_prop
  have hg' : deriv g (1 - rho) ≠ 0 := by
    dsimp [g]
    rw [deriv_const_sub]
    norm_num
  calc
    analyticOrderAt bcfXi (1 - rho) =
        analyticOrderAt (bcfXi ∘ g) (1 - rho) := by
      apply analyticOrderAt_congr
      filter_upwards with z
      simpa [Function.comp_def, g] using (bcfXi_one_sub z).symm
    _ = analyticOrderAt bcfXi (g (1 - rho)) :=
      analyticOrderAt_comp_of_deriv_ne_zero hg hg'
    _ = analyticOrderAt bcfXi rho := by
      dsimp [g]
      congr 1
      ring

/-- The elementary canonical-product factor contributed by one zero with its
analytic multiplicity. -/
def bcfXiCanonicalFactor (rho : ℂ) (s : ℂ) : ℂ :=
  (1 - s / rho) ^ bcfXiZeroMultiplicity rho

/-- The finite canonical product over the nontrivial zeros in a height
truncation. -/
def bcfXiFiniteCanonicalProduct (T : ℝ) (s : ℂ) : ℂ :=
  ∏ rho ∈ bcfZerosUpToHeight T, bcfXiCanonicalFactor rho s

theorem differentiableAt_bcfXiCanonicalFactor (rho s : ℂ) :
    DifferentiableAt ℂ (bcfXiCanonicalFactor rho) s := by
  unfold bcfXiCanonicalFactor
  fun_prop

theorem logDeriv_bcfXiCanonicalBase_zero {rho : ℂ} :
    logDeriv (fun s : ℂ ↦ 1 - s / rho) 0 = -rho⁻¹ := by
  have hderiv :
      HasDerivAt (fun s : ℂ ↦ 1 - s / rho) (-rho⁻¹) 0 := by
    convert ((hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub
      ((hasDerivAt_id (𝕜 := ℂ) 0).div_const rho)) using 1
    all_goals ring
  rw [logDeriv_apply, hderiv.deriv]
  simp

theorem logDeriv_bcfXiCanonicalBase_one {rho : ℂ}
    (hrho0 : rho ≠ 0) (hrho1 : rho ≠ 1) :
    logDeriv (fun s : ℂ ↦ 1 - s / rho) 1 = (1 - rho)⁻¹ := by
  have hderiv :
      HasDerivAt (fun s : ℂ ↦ 1 - s / rho) (-rho⁻¹) 1 := by
    convert ((hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub
      ((hasDerivAt_id (𝕜 := ℂ) 1).div_const rho)) using 1
    all_goals ring
  rw [logDeriv_apply, hderiv.deriv]
  have hsub : 1 - rho ≠ 0 := sub_ne_zero.mpr (Ne.symm hrho1)
  have hsub' : rho - 1 ≠ 0 := by
    have heq : rho - 1 = -(1 - rho) := by ring
    rw [heq]
    exact neg_ne_zero.mpr hsub
  field_simp [hrho0, hsub, hsub']
  ring

theorem logDeriv_bcfXiCanonicalFactor_zero (rho : ℂ) :
    logDeriv (bcfXiCanonicalFactor rho) 0 =
      (bcfXiZeroMultiplicity rho : ℂ) * (-rho⁻¹) := by
  unfold bcfXiCanonicalFactor
  have hdiff : DifferentiableAt ℂ (fun s : ℂ ↦ 1 - s / rho) 0 := by
    fun_prop
  rw [logDeriv_fun_pow hdiff (bcfXiZeroMultiplicity rho)]
  rw [logDeriv_bcfXiCanonicalBase_zero]

theorem logDeriv_bcfXiCanonicalFactor_one {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    logDeriv (bcfXiCanonicalFactor rho) 1 =
      (bcfXiZeroMultiplicity rho : ℂ) * (1 - rho)⁻¹ := by
  unfold bcfXiCanonicalFactor
  have hdiff : DifferentiableAt ℂ (fun s : ℂ ↦ 1 - s / rho) 1 := by
    fun_prop
  rw [logDeriv_fun_pow hdiff (bcfXiZeroMultiplicity rho)]
  rw [logDeriv_bcfXiCanonicalBase_one (bcfZero_ne_zero hrho) (bcfZero_ne_one hrho)]

theorem bcfXiCanonicalFactor_zero_ne_zero (rho : ℂ) :
    bcfXiCanonicalFactor rho 0 ≠ 0 := by
  simp [bcfXiCanonicalFactor]

theorem bcfXiCanonicalFactor_one_ne_zero {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    bcfXiCanonicalFactor rho 1 ≠ 0 := by
  unfold bcfXiCanonicalFactor
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro h
  apply bcfZero_ne_one hrho
  have hmul := (eq_div_iff (bcfZero_ne_zero hrho)).mp h
  simpa using hmul

theorem differentiableAt_bcfXiFiniteCanonicalProduct (T : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (bcfXiFiniteCanonicalProduct T) s := by
  unfold bcfXiFiniteCanonicalProduct
  apply DifferentiableAt.fun_finsetProd
  intro rho hrho
  exact differentiableAt_bcfXiCanonicalFactor rho s

theorem logDeriv_bcfXiFiniteCanonicalProduct_eq_sum
    (T : ℝ) (s : ℂ)
    (hnonzero : ∀ rho ∈ bcfZerosUpToHeight T,
      bcfXiCanonicalFactor rho s ≠ 0) :
    logDeriv (bcfXiFiniteCanonicalProduct T) s =
      ∑ rho ∈ bcfZerosUpToHeight T, logDeriv (bcfXiCanonicalFactor rho) s := by
  unfold bcfXiFiniteCanonicalProduct
  rw [logDeriv_prod hnonzero]
  intro rho hrho
  exact differentiableAt_bcfXiCanonicalFactor rho s

/-- At every finite height, the canonical product's endpoint
logarithmic-derivative difference is precisely the finite BCF Hadamard
endpoint sum. -/
theorem bcfXiFiniteCanonicalProduct_endpointDifference (T : ℝ) :
    logDeriv (bcfXiFiniteCanonicalProduct T) 1 -
        logDeriv (bcfXiFiniteCanonicalProduct T) 0 =
      bcfHadamardEndpointSumUpToHeight T := by
  rw [logDeriv_bcfXiFiniteCanonicalProduct_eq_sum T 1
    (fun rho hrho ↦ bcfXiCanonicalFactor_one_ne_zero hrho)]
  rw [logDeriv_bcfXiFiniteCanonicalProduct_eq_sum T 0
    (fun rho _ ↦ bcfXiCanonicalFactor_zero_ne_zero rho)]
  rw [← Finset.sum_sub_distrib]
  unfold bcfHadamardEndpointSumUpToHeight
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [logDeriv_bcfXiCanonicalFactor_one hrho,
    logDeriv_bcfXiCanonicalFactor_zero]
  unfold bcfHadamardEndpointTerm
  ring

end

end NBMellinTools.H15BCF
