/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import NBMellinTools.H15BCF.CanonicalProductFinite

/-!
# Finite genus-one products for the BCF xi function

The genus-one factor at a zero `rho` is

`E₁(s / rho) = (1 - s / rho) * exp (s / rho)`.

The exponential correction is indispensable in the infinite Hadamard product:
it makes the factors differ from `1` by a second-order term.  This file proves
the exact finite endpoint calculation.  In particular, the extra exponential
has the same logarithmic derivative at `0` and `1`, so its contribution
cancels in the endpoint difference.

The last definitions precisely record, but do not assume, the three analytic
ingredients still absent from Mathlib: absolute convergence, identification
with xi up to `exp (A + B * s)`, and justified differentiation of the product.
The zeros are counted with their analytic multiplicities throughout.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- The genus-one elementary factor before its zero multiplicity is applied. -/
def bcfXiGenusOneBase (rho s : ℂ) : ℂ :=
  (1 - s / rho) * exp (s / rho)

/-- The multiplicity-aware genus-one factor contributed by one nontrivial
zero of xi. -/
def bcfXiGenusOneFactor (rho s : ℂ) : ℂ :=
  (bcfXiGenusOneBase rho s) ^ bcfXiZeroMultiplicity rho

/-- The finite genus-one product over the nontrivial zeros in a height
truncation. -/
def bcfXiFiniteGenusOneProduct (T : ℝ) (s : ℂ) : ℂ :=
  ∏ rho ∈ bcfZerosUpToHeight T, bcfXiGenusOneFactor rho s

theorem differentiableAt_bcfXiGenusOneBase (rho s : ℂ) :
    DifferentiableAt ℂ (bcfXiGenusOneBase rho) s := by
  unfold bcfXiGenusOneBase
  fun_prop

theorem logDeriv_bcfXiGenusOneExp (rho x : ℂ) :
    logDeriv (fun s : ℂ ↦ exp (s / rho)) x = rho⁻¹ := by
  have hderiv :
      HasDerivAt (fun s : ℂ ↦ exp (s / rho)) (exp (x / rho) * rho⁻¹) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using
      ((hasDerivAt_id (𝕜 := ℂ) x).div_const rho).cexp
  rw [logDeriv_apply, hderiv.deriv]
  field_simp [Complex.exp_ne_zero]

theorem bcfXiGenusOneBase_zero (rho : ℂ) :
    bcfXiGenusOneBase rho 0 = 1 := by
  simp [bcfXiGenusOneBase]

theorem bcfXiGenusOneBase_one_ne_zero {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    bcfXiGenusOneBase rho 1 ≠ 0 := by
  unfold bcfXiGenusOneBase
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro h
    apply bcfZero_ne_one hrho
    have hmul := (eq_div_iff (bcfZero_ne_zero hrho)).mp h
    simpa using hmul
  · exact Complex.exp_ne_zero _

theorem logDeriv_bcfXiGenusOneBase_zero (rho : ℂ) :
    logDeriv (bcfXiGenusOneBase rho) 0 = 0 := by
  unfold bcfXiGenusOneBase
  rw [logDeriv_mul 0]
  · rw [logDeriv_bcfXiCanonicalBase_zero,
      logDeriv_bcfXiGenusOneExp]
    ring
  · simp
  · exact Complex.exp_ne_zero _
  · fun_prop
  · fun_prop

theorem logDeriv_bcfXiGenusOneBase_one {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    logDeriv (bcfXiGenusOneBase rho) 1 = (1 - rho)⁻¹ + rho⁻¹ := by
  unfold bcfXiGenusOneBase
  rw [logDeriv_mul 1]
  · rw [logDeriv_bcfXiCanonicalBase_one
      (bcfZero_ne_zero hrho) (bcfZero_ne_one hrho),
      logDeriv_bcfXiGenusOneExp]
  · apply sub_ne_zero.mpr
    intro h
    apply bcfZero_ne_one hrho
    have hmul := (eq_div_iff (bcfZero_ne_zero hrho)).mp h
    simpa using hmul
  · exact Complex.exp_ne_zero _
  · fun_prop
  · fun_prop

theorem differentiableAt_bcfXiGenusOneFactor (rho s : ℂ) :
    DifferentiableAt ℂ (bcfXiGenusOneFactor rho) s := by
  unfold bcfXiGenusOneFactor
  exact (differentiableAt_bcfXiGenusOneBase rho s).pow _

theorem bcfXiGenusOneFactor_zero_ne_zero (rho : ℂ) :
    bcfXiGenusOneFactor rho 0 ≠ 0 := by
  unfold bcfXiGenusOneFactor
  rw [bcfXiGenusOneBase_zero]
  simp

theorem bcfXiGenusOneFactor_one_ne_zero {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    bcfXiGenusOneFactor rho 1 ≠ 0 := by
  unfold bcfXiGenusOneFactor
  exact pow_ne_zero _ (bcfXiGenusOneBase_one_ne_zero hrho)

theorem logDeriv_bcfXiGenusOneFactor_zero (rho : ℂ) :
    logDeriv (bcfXiGenusOneFactor rho) 0 = 0 := by
  unfold bcfXiGenusOneFactor
  rw [logDeriv_fun_pow (differentiableAt_bcfXiGenusOneBase rho 0)]
  rw [logDeriv_bcfXiGenusOneBase_zero]
  ring

theorem logDeriv_bcfXiGenusOneFactor_one {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    logDeriv (bcfXiGenusOneFactor rho) 1 =
      (bcfXiZeroMultiplicity rho : ℂ) * ((1 - rho)⁻¹ + rho⁻¹) := by
  unfold bcfXiGenusOneFactor
  rw [logDeriv_fun_pow (differentiableAt_bcfXiGenusOneBase rho 1)]
  rw [logDeriv_bcfXiGenusOneBase_one hrho]

theorem differentiableAt_bcfXiFiniteGenusOneProduct (T : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (bcfXiFiniteGenusOneProduct T) s := by
  unfold bcfXiFiniteGenusOneProduct
  apply DifferentiableAt.fun_finsetProd
  intro rho hrho
  exact differentiableAt_bcfXiGenusOneFactor rho s

theorem logDeriv_bcfXiFiniteGenusOneProduct_eq_sum
    (T : ℝ) (s : ℂ)
    (hnonzero : ∀ rho ∈ bcfZerosUpToHeight T,
      bcfXiGenusOneFactor rho s ≠ 0) :
    logDeriv (bcfXiFiniteGenusOneProduct T) s =
      ∑ rho ∈ bcfZerosUpToHeight T, logDeriv (bcfXiGenusOneFactor rho) s := by
  unfold bcfXiFiniteGenusOneProduct
  rw [logDeriv_prod hnonzero]
  intro rho hrho
  exact differentiableAt_bcfXiGenusOneFactor rho s

/-- The genus-one correction cancels exactly between the two xi endpoints.
This is the finite algebra needed by the genuine infinite Hadamard route. -/
theorem bcfXiFiniteGenusOneProduct_endpointDifference (T : ℝ) :
    logDeriv (bcfXiFiniteGenusOneProduct T) 1 -
        logDeriv (bcfXiFiniteGenusOneProduct T) 0 =
      bcfHadamardEndpointSumUpToHeight T := by
  rw [logDeriv_bcfXiFiniteGenusOneProduct_eq_sum T 1
    (fun rho hrho ↦ bcfXiGenusOneFactor_one_ne_zero hrho)]
  rw [logDeriv_bcfXiFiniteGenusOneProduct_eq_sum T 0
    (fun rho _ ↦ bcfXiGenusOneFactor_zero_ne_zero rho)]
  rw [← Finset.sum_sub_distrib]
  unfold bcfHadamardEndpointSumUpToHeight
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [logDeriv_bcfXiGenusOneFactor_one hrho,
    logDeriv_bcfXiGenusOneFactor_zero]
  unfold bcfHadamardEndpointTerm
  ring

/-- The intended infinite genus-one product, indexed by distinct nontrivial
zeros and with each factor raised to its analytic multiplicity. -/
def bcfXiInfiniteGenusOneProduct (s : ℂ) : ℂ :=
  ∏' rho : bcfNontrivialZetaZeros, bcfXiGenusOneFactor (rho : ℂ) s

/-- Absolute convergence of the deviations of the genus-one factors from one.
This is a classical zero-counting consequence, not currently proved by
Mathlib. -/
def BCFGenusOneProductAbsoluteConvergence : Prop :=
  ∀ s : ℂ, Summable (fun rho : bcfNontrivialZetaZeros ↦
    bcfXiGenusOneFactor (rho : ℂ) s - 1)

/-- Pointwise existence of the infinite genus-one product.  This is weaker
than locally uniform convergence, but follows directly from summability of
the factor deviations. -/
def BCFGenusOneProductPointwiseMultipliable : Prop :=
  ∀ s : ℂ, Multipliable (fun rho : bcfNontrivialZetaZeros ↦
    bcfXiGenusOneFactor (rho : ℂ) s)

/-- The stated absolute-convergence target already supplies a genuine
pointwise infinite product through Mathlib's general infinite-product API.
It does not supply the locally uniform convergence or derivative control
needed for the Hadamard endpoint formula. -/
theorem bcfGenusOneProduct_pointwiseMultipliable_of_absoluteConvergence
    (habs : BCFGenusOneProductAbsoluteConvergence) :
    BCFGenusOneProductPointwiseMultipliable := by
  intro s
  convert Complex.multipliable_one_add_of_summable (habs s) using 1
  funext rho
  ring

theorem bcfXiGenusOneFactor_one_ne_zero_of_nontrivial
    (rho : bcfNontrivialZetaZeros) :
    bcfXiGenusOneFactor (rho : ℂ) 1 ≠ 0 := by
  exact bcfXiGenusOneFactor_one_ne_zero
    (T := abs ((rho : ℂ).im)) (rho := rho)
    (by
      rw [mem_bcfZerosUpToHeight]
      have hrho := (mem_bcfNontrivialZetaZeros.mp rho.property)
      exact ⟨hrho.1, hrho.2.1, hrho.2.2, le_rfl⟩)

/-- Absolute convergence ensures that the two endpoint products themselves
are nonzero.  No simplicity or RH assumption is used here: multiplicities
are already built into every factor. -/
theorem bcfXiInfiniteGenusOneProduct_endpoint_ne_zero_of_absoluteConvergence
    (habs : BCFGenusOneProductAbsoluteConvergence) (x : ℂ)
    (hx : x = 0 ∨ x = 1) :
    bcfXiInfiniteGenusOneProduct x ≠ 0 := by
  unfold bcfXiInfiniteGenusOneProduct
  have hproduct :
      ∏' rho : bcfNontrivialZetaZeros,
        (1 + (bcfXiGenusOneFactor (rho : ℂ) x - 1)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable
      (f := fun rho : bcfNontrivialZetaZeros ↦
        bcfXiGenusOneFactor (rho : ℂ) x - 1)
      (by
        intro rho
        rw [add_sub_cancel]
        rcases hx with rfl | rfl
        · exact bcfXiGenusOneFactor_zero_ne_zero rho
        · exact bcfXiGenusOneFactor_one_ne_zero_of_nontrivial rho)
      (habs x).norm
  rw [tprod_congr fun rho ↦ (add_sub_cancel _ _).symm]
  exact hproduct

/-- The deviation from one of a multiplicity-aware genus-one factor.  The
classical zero-counting estimate must bound this quantity uniformly on compact
sets. -/
def bcfXiGenusOneDeviation (rho : bcfNontrivialZetaZeros) (s : ℂ) : ℂ :=
  bcfXiGenusOneFactor (rho : ℂ) s - 1

theorem continuous_bcfXiGenusOneDeviation (rho : bcfNontrivialZetaZeros) :
    Continuous (bcfXiGenusOneDeviation rho) := by
  unfold bcfXiGenusOneDeviation bcfXiGenusOneFactor bcfXiGenusOneBase
  fun_prop

/-- A summable Weierstrass majorant for the genus-one deviations on a compact
set.  This is the exact output required from the missing zero-counting and
factor estimates. -/
def BCFGenusOneCompactMajorant (K : Set ℂ) : Prop :=
  ∃ u : bcfNontrivialZetaZeros → ℝ, Summable u ∧
    ∀ rho : bcfNontrivialZetaZeros, ∀ s ∈ K,
      ‖bcfXiGenusOneDeviation rho s‖ ≤ u rho

/-- A compact majorant gives absolute convergence at every point of that
compact set. -/
theorem bcfGenusOneProduct_summableAt_of_compactMajorant
    {K : Set ℂ} (hmajorant : BCFGenusOneCompactMajorant K)
    {s : ℂ} (hs : s ∈ K) :
    Summable (fun rho : bcfNontrivialZetaZeros ↦
      bcfXiGenusOneFactor (rho : ℂ) s - 1) := by
  rcases hmajorant with ⟨u, hu, hbound⟩
  apply hu.of_norm_bounded
  intro rho
  exact hbound rho s hs

/-- A compact-set majorant gives uniform convergence of the genus-one product
on that compact set by Mathlib's Weierstrass theorem for infinite products. -/
theorem bcfGenusOneProduct_multipliableUniformlyOn_of_compactMajorant
    {K : Set ℂ} (hK : IsCompact K) (hmajorant : BCFGenusOneCompactMajorant K) :
    MultipliableUniformlyOn
      (fun rho : bcfNontrivialZetaZeros ↦ fun s : ℂ ↦
        bcfXiGenusOneFactor (rho : ℂ) s) K := by
  rcases hmajorant with ⟨u, hu, hbound⟩
  have hproduct : MultipliableUniformlyOn
      (fun rho : bcfNontrivialZetaZeros ↦ fun s : ℂ ↦
        1 + bcfXiGenusOneDeviation rho s) K := by
    apply hu.multipliableUniformlyOn_one_add hK
    · filter_upwards with rho
      intro s hs
      exact hbound rho s hs
    · intro rho
      exact (continuous_bcfXiGenusOneDeviation rho).continuousOn
  convert hproduct using 1
  funext rho s
  unfold bcfXiGenusOneDeviation
  ring

/-- The locally uniform majorant condition needed by the full Hadamard
product.  It is deliberately stated over arbitrary compact subsets of an open
region, rather than assuming an unjustified global bound in `s`. -/
def BCFGenusOneLocallySummableMajorantOn (Omega : Set ℂ) : Prop :=
  ∀ K : Set ℂ, K ⊆ Omega → IsCompact K → BCFGenusOneCompactMajorant K

/-- A locally summable majorant on the whole plane supplies the previously
named pointwise absolute-convergence target. -/
theorem bcfGenusOneProduct_absoluteConvergence_of_locallyMajorant_univ
    (hmajorant : BCFGenusOneLocallySummableMajorantOn Set.univ) :
    BCFGenusOneProductAbsoluteConvergence := by
  intro s
  apply bcfGenusOneProduct_summableAt_of_compactMajorant
    (hmajorant {s} (Set.subset_univ _) isCompact_singleton)
  exact Set.mem_singleton _

/-- Compact majorants assemble into a locally uniform genus-one product on an
open region.  The sole unproved analytic input is now the named majorant
condition above. -/
theorem bcfGenusOneProduct_multipliableLocallyUniformlyOn_of_majorant
    {Omega : Set ℂ} (hopen : IsOpen Omega)
    (hmajorant : BCFGenusOneLocallySummableMajorantOn Omega) :
    MultipliableLocallyUniformlyOn
      (fun rho : bcfNontrivialZetaZeros ↦ fun s : ℂ ↦
        bcfXiGenusOneFactor (rho : ℂ) s) Omega := by
  exact (hasProdLocallyUniformlyOn_of_forall_compact
    (f := fun rho : bcfNontrivialZetaZeros ↦ fun s : ℂ ↦
      bcfXiGenusOneFactor (rho : ℂ) s)
    (g := fun s : ℂ ↦ ∏' rho : bcfNontrivialZetaZeros,
      bcfXiGenusOneFactor (rho : ℂ) s)
    hopen
    (fun K hKOmega hK ↦
      (bcfGenusOneProduct_multipliableUniformlyOn_of_compactMajorant hK
        (hmajorant K hKOmega hK)).hasProdUniformlyOn)).multipliableLocallyUniformlyOn

/-- The full xi Hadamard factorization has an indispensable exponential
prefactor.  The linear term `B * s` cancels from the endpoint logarithmic
derivative difference, but it must be retained in the factorization itself. -/
def BCFXiGenusOneFactorization : Prop :=
  ∃ A B : ℂ, ∀ s : ℂ,
    bcfXi s = exp (A + B * s) * bcfXiInfiniteGenusOneProduct s

/-- The endpoint form of termwise logarithmic differentiation required by the
BCF constant calculation.  Locally uniform convergence alone is not enough:
the derivative limit must be justified at both endpoints. -/
def BCFGenusOneEndpointLogDerivConvergence : Prop :=
  Tendsto (fun T : ℝ ↦ logDeriv (bcfXiFiniteGenusOneProduct T) 0) atTop
      (𝓝 (logDeriv bcfXiInfiniteGenusOneProduct 0)) ∧
    Tendsto (fun T : ℝ ↦ logDeriv (bcfXiFiniteGenusOneProduct T) 1) atTop
      (𝓝 (logDeriv bcfXiInfiniteGenusOneProduct 1))

theorem logDeriv_bcfXiAffineExp (A B x : ℂ) :
    logDeriv (fun s : ℂ ↦ exp (A + B * s)) x = B := by
  have hderiv :
      HasDerivAt (fun s : ℂ ↦ exp (A + B * s)) (exp (A + B * x) * B) x := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_const (x := x) (c := A)).add
        ((hasDerivAt_const (x := x) (c := B)).mul
          (hasDerivAt_id (𝕜 := ℂ) x))).cexp
  rw [logDeriv_apply, hderiv.deriv]
  field_simp [Complex.exp_ne_zero]

/-- A genus-one factorization identifies the endpoint difference of the
infinite product with the corresponding xi difference.  The coefficient `B`
appears in each logarithmic derivative and cancels only after subtraction. -/
theorem bcfXiInfiniteGenusOneProduct_endpointDifference_of_factorization
    (hfactor : BCFXiGenusOneFactorization) :
    logDeriv bcfXiInfiniteGenusOneProduct 1 -
        logDeriv bcfXiInfiniteGenusOneProduct 0 =
      -2 * logDeriv bcfXi 0 := by
  rcases hfactor with ⟨A, B, hfactor⟩
  let P : ℂ → ℂ := bcfXiInfiniteGenusOneProduct
  have hP_formula : P = fun s : ℂ ↦ exp (-(A + B * s)) * bcfXi s := by
    funext s
    dsimp [P]
    rw [hfactor s, ← mul_assoc, ← Complex.exp_add]
    ring_nf
    simp
  have hP_diff : ∀ x : ℂ, DifferentiableAt ℂ P x := by
    intro x
    rw [hP_formula]
    apply DifferentiableAt.mul
    · fun_prop
    · exact differentiable_bcfXi.differentiableAt
  have hP_nonzero : ∀ x : ℂ, bcfXi x ≠ 0 → P x ≠ 0 := by
    intro x hxi hzero
    have : bcfXi x = 0 := by
      rw [hfactor x]
      change exp (A + B * x) * P x = 0
      rw [hzero, mul_zero]
    exact hxi this
  have hlog : ∀ x : ℂ, bcfXi x ≠ 0 →
      logDeriv bcfXi x = B + logDeriv P x := by
    intro x hxi
    rw [show bcfXi = fun s : ℂ ↦ exp (A + B * s) * P s from funext hfactor]
    rw [logDeriv_mul (f := fun s : ℂ ↦ exp (A + B * s)) (g := P) x
      (Complex.exp_ne_zero _) (hP_nonzero x hxi) (by fun_prop) (hP_diff x),
      logDeriv_bcfXiAffineExp]
  have hzero := hlog 0 bcfXi_zero_ne_zero
  have hone := hlog 1 bcfXi_one_ne_zero
  have hendpoint :
      logDeriv P 1 - logDeriv P 0 =
        logDeriv bcfXi 1 - logDeriv bcfXi 0 := by
    rw [hone, hzero]
    ring
  rw [show bcfXiInfiniteGenusOneProduct = P by rfl, hendpoint]
  exact bcfXi_logDeriv_endpointDifference

/-- The finite genus-one calculation plus the two genuine analytic product
inputs imply the missing xi endpoint formula.  Absolute convergence is a
separate prerequisite for constructing the infinite product; the present
deduction uses its supplied factorization and derivative-limit consequences. -/
theorem bcfHadamardEndpointFormula_of_genusOneProduct
    (hfactor : BCFXiGenusOneFactorization)
    (hderiv : BCFGenusOneEndpointLogDerivConvergence) :
    BCFHadamardEndpointFormula := by
  unfold BCFHadamardEndpointFormula
  have hlimit :
      Tendsto bcfHadamardEndpointSumUpToHeight atTop
        (𝓝 (logDeriv bcfXiInfiniteGenusOneProduct 1 -
          logDeriv bcfXiInfiniteGenusOneProduct 0)) := by
    have hsub := hderiv.2.sub hderiv.1
    refine hsub.congr' ?_
    filter_upwards with T
    exact bcfXiFiniteGenusOneProduct_endpointDifference T
  rw [bcfXiInfiniteGenusOneProduct_endpointDifference_of_factorization hfactor] at hlimit
  exact hlimit

end

end NBMellinTools.H15BCF
