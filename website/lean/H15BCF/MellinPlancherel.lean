/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.MellinInversion
import NBMellinTools.FourierPlancherel
import NBMellinTools.H15BCF.MellinTransform
import NBMellinTools.NB3MellinContinuity

/-!
# Conditional BCF formalization: critical-line Plancherel identity

Mathlib already proves `mellin_eq_fourier` and supplies the Fourier transform
as a linear isometry on `L²`. This file records the exact logarithmic
pullback and the BCF critical-line integrand, proves the weighted change of
variables, and applies the `L¹ ∩ L²` Fourier bridge from
`NBMellinTools.FourierPlancherel`.

The main result `bcfMellinPlancherel` closes Phase 3 unconditionally: the
finite BCF Gram energy is exactly its weighted critical-line integral.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open MeasureTheory Complex Real Set
open scoped FourierTransform
open NBMellinTools.NB2

/-- The point `1/2 + it` on the critical line. -/
def criticalLine (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (t : ℂ) * I

/-- The logarithmic pullback which converts the Mellin transform on
`re s = σ` into a Fourier transform. -/
def mellinLogPullback (σ : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(σ : ℂ) * (u : ℂ)) * f (Real.exp (-u))

private def rexpNeg : ℝ → ℝ :=
  Real.exp ∘ Neg.neg

private theorem rexpNeg_deriv :
    ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt rexpNeg (-Real.exp (-u)) Set.univ u := by
  intro u hu
  unfold rexpNeg
  exact mul_neg_one (Real.exp (-u)) ▸
    ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt

private theorem rexpNeg_image :
    rexpNeg '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
  rw [show rexpNeg = Real.exp ∘ Neg.neg by rfl, Set.image_comp,
    Set.image_univ_of_surjective neg_surjective, Set.image_univ,
    Real.range_exp]

private theorem rexpNeg_injOn :
    (Set.univ : Set ℝ).InjOn rexpNeg := by
  exact Real.exp_injective.injOn.comp neg_injective.injOn
    (Set.univ.mapsTo_univ _)

private theorem rexp_cexp_weight
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : ℝ) (s : ℂ) (z : E) :
    rexp (-u) • cexp (-↑u) ^ (s - 1) • z = cexp (-s * ↑u) • z := by
  change (rexp (-u) : ℂ) • _ = _ • z
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _),
    cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  ring_nf

/-- Mellin convergence at a real abscissa is equivalent to integrability of
the associated logarithmic pullback. -/
theorem mellinConvergent_real_iff_integrable_pullback
    (f : ℝ → ℂ) (σ : ℝ) :
    MellinConvergent f (σ : ℂ) ↔ Integrable (mellinLogPullback σ f) := by
  rw [MellinConvergent, ← rexpNeg_image,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexpNeg_deriv rexpNeg_injOn]
  simp only [IntegrableOn, Measure.restrict_univ]
  apply integrable_congr
  filter_upwards with u
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]
  simpa [rexpNeg, mellinLogPullback, smul_eq_mul] using
    rexp_cexp_weight u (σ : ℂ) (f (Real.exp (-u)))

/-- At weight `1/2`, the squared norm of the logarithmic pullback includes
exactly the Jacobian needed for the substitution `x = exp (-u)`. -/
theorem mellinLogPullback_norm_sq (f : ℝ → ℂ) (u : ℝ) :
    ‖mellinLogPullback (1 / 2) f u‖ ^ 2 =
      Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2 := by
  rw [mellinLogPullback, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [show -(1 / 2 : ℝ) * u = -u / 2 by ring, mul_pow]
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- Weighted `L²` change of variables for the logarithmic Mellin pullback. -/
theorem integral_mellinLogPullback_norm_sq (f : ℝ → ℂ) :
    (∫ u : ℝ, ‖mellinLogPullback (1 / 2) f u‖ ^ 2) =
      ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  rw [← rexpNeg_image, integral_image_eq_integral_abs_deriv_smul
    MeasurableSet.univ rexpNeg_deriv rexpNeg_injOn]
  simp only [Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards with u
  rw [mellinLogPullback_norm_sq]
  simp [rexpNeg, abs_of_pos (Real.exp_pos _), smul_eq_mul]

/-- Integrability form of the weighted logarithmic change of variables. -/
theorem integrable_mellinLogPullback_norm_sq_iff (f : ℝ → ℂ) :
    Integrable (fun u : ℝ ↦ ‖mellinLogPullback (1 / 2) f u‖ ^ 2) ↔
      IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2) (Set.Ioi 0) := by
  rw [← rexpNeg_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexpNeg_deriv rexpNeg_injOn]
  simp only [IntegrableOn, Measure.restrict_univ]
  apply integrable_congr
  filter_upwards with u
  rw [mellinLogPullback_norm_sq]
  simp [rexpNeg, abs_of_pos (Real.exp_pos _), smul_eq_mul]

@[simp]
theorem criticalLine_re (t : ℝ) :
    (criticalLine t).re = 1 / 2 := by
  simp [criticalLine]

@[simp]
theorem criticalLine_im (t : ℝ) :
    (criticalLine t).im = t := by
  simp [criticalLine]

/-- Mellin on the critical line is the Fourier transform of the logarithmic
pullback, evaluated at frequency `t / (2π)`. -/
theorem mellin_criticalLine_eq_fourier (f : ℝ → ℂ) (t : ℝ) :
    mellin f (criticalLine t) =
      𝓕 (mellinLogPullback (1 / 2) f) (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun :
      (fun u : ℝ =>
        Real.exp (-(criticalLine t).re * u) • f (Real.exp (-u))) =
      mellinLogPullback (1 / 2) f := by
    funext u
    unfold mellinLogPullback
    simp [criticalLine]
  rw [hfun, criticalLine_im]

/-- The exact BCF zeta-polynomial numerator on the critical line. -/
def bcfCriticalLineNumerator (N : ℕ) (t : ℝ) : ℂ :=
  1 - riemannZeta (criticalLine t) *
    bcfDirichletPolynomial N (criticalLine t)

/-- The real integrand appearing on the right side of the BCF
Mellin--Plancherel identity. -/
def bcfCriticalLineIntegrand (N : ℕ) (t : ℝ) : ℝ :=
  ‖bcfCriticalLineNumerator N t‖ ^ 2 / (1 / 4 + t ^ 2)

/-- The prospective critical-line expression for the BCF energy. -/
def bcfCriticalLineEnergy (N : ℕ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t : ℝ, bcfCriticalLineIntegrand N t

/-- Exact Mellin evaluation at a point of the critical line. -/
theorem bcfMellinTransform_criticalLine (N : ℕ) (t : ℝ) :
    mellin (fun x : ℝ => (bcfApproximationError N x : ℂ))
        (criticalLine t) =
      bcfCriticalLineNumerator N t / criticalLine t := by
  apply bcfMellinTransform
  · rw [criticalLine_re]
    norm_num
  · rw [criticalLine_re]
    norm_num

/-- The squared norm of a critical-line point is the classical denominator
`1/4 + t²`. -/
theorem normSq_criticalLine (t : ℝ) :
    ‖criticalLine t‖ ^ 2 = 1 / 4 + t ^ 2 := by
  rw [Complex.sq_norm]
  simp [criticalLine, Complex.normSq_apply]
  ring

/-- The zeta-polynomial integrand is exactly the squared norm of the Mellin
transform of the BCF approximation error. -/
theorem bcfCriticalLineIntegrand_eq_norm_mellin_sq
    (N : ℕ) (t : ℝ) :
    bcfCriticalLineIntegrand N t =
      ‖mellin (fun x : ℝ => (bcfApproximationError N x : ℂ))
        (criticalLine t)‖ ^ 2 := by
  rw [bcfMellinTransform_criticalLine]
  unfold bcfCriticalLineIntegrand
  rw [norm_div, div_pow, normSq_criticalLine]

/-- The complex-valued BCF approximation error belongs to
`L²((0, ∞), dx)`. -/
theorem bcfApproximationError_memLp_two (N : ℕ) :
    MemLp (fun x : ℝ ↦ (bcfApproximationError N x : ℂ)) 2
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hreal := NBMellinTools.NB3.baezDuarteError_memLp_two N
    (fun k ↦ -bcfCoefficient N (k.val + 1))
  have hcomplex : MemLp
      (fun x : ℝ ↦ ((chi01 x - bdApprox N
        (fun k ↦ -bcfCoefficient N (k.val + 1)) x : ℝ) : ℂ)) 2
      (volume.restrict (Set.Ioi (0 : ℝ))) := hreal.ofReal
  apply hcomplex.ae_eq
  filter_upwards with x
  exact_mod_cast
    (bcfApproximationError_eq_chi_sub_bdApprox N x).symm

/-- The BCF logarithmic pullback is integrable. This is the `L¹` input
needed to identify its pointwise Fourier integral. -/
theorem bcfMellinLogPullback_integrable (N : ℕ) :
    Integrable (mellinLogPullback (1 / 2)
      (fun x : ℝ ↦ (bcfApproximationError N x : ℂ))) := by
  apply (mellinConvergent_real_iff_integrable_pullback _ (1 / 2)).1
  apply bcfApproximationError_mellinConvergent
  · norm_num
  · norm_num

/-- The BCF logarithmic pullback belongs to `L²(ℝ)`. -/
theorem bcfMellinLogPullback_memLp_two (N : ℕ) :
    MemLp (mellinLogPullback (1 / 2)
      (fun x : ℝ ↦ (bcfApproximationError N x : ℂ))) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (bcfMellinLogPullback_integrable N).aestronglyMeasurable).2
  apply (integrable_mellinLogPullback_norm_sq_iff _).2
  exact (bcfApproximationError_memLp_two N).integrable_norm_pow (by norm_num)

/-- Exact Mellin--Plancherel identity for one finite BCF approximant. -/
theorem bcfGramEnergy_eq_criticalLineEnergy (N : ℕ) :
    bcfGramEnergy N = bcfCriticalLineEnergy N := by
  let f : ℝ → ℂ := fun x ↦ (bcfApproximationError N x : ℂ)
  let g : ℝ → ℂ := mellinLogPullback (1 / 2) f
  have hg1 : Integrable g := bcfMellinLogPullback_integrable N
  have hg2 : MemLp g 2 := bcfMellinLogPullback_memLp_two N
  have hscale :
      (∫ t : ℝ, ‖𝓕 g (t / (2 * Real.pi))‖ ^ 2) =
        (2 * Real.pi) * ∫ y : ℝ, ‖𝓕 g y‖ ^ 2 := by
    have h2pi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    simpa [abs_of_pos h2pi, smul_eq_mul] using
      (Measure.integral_comp_div (fun y : ℝ ↦ ‖𝓕 g y‖ ^ 2)
        (2 * Real.pi))
  rw [bcfCriticalLineEnergy]
  calc
    bcfGramEnergy N = ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
      unfold bcfGramEnergy f
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp [Complex.norm_real, sq_abs]
    _ = ∫ u : ℝ, ‖g u‖ ^ 2 :=
      (integral_mellinLogPullback_norm_sq f).symm
    _ = ∫ y : ℝ, ‖𝓕 g y‖ ^ 2 :=
      (integral_norm_sq_fourier_eq hg1 hg2).symm
    _ = (1 / (2 * Real.pi)) *
        ∫ t : ℝ, ‖𝓕 g (t / (2 * Real.pi))‖ ^ 2 := by
      rw [hscale]
      field_simp
    _ = (1 / (2 * Real.pi)) *
        ∫ t : ℝ, bcfCriticalLineIntegrand N t := by
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [bcfCriticalLineIntegrand_eq_norm_mellin_sq,
        mellin_criticalLine_eq_fourier]

/-- The exact Mellin--Plancherel statement for every finite BCF error. -/
def BCFMellinPlancherel : Prop :=
  ∀ N : ℕ, bcfGramEnergy N = bcfCriticalLineEnergy N

/-- Phase 3: the finite BCF Gram energy equals the weighted critical-line
integral of `|1 - ζ(s) V_N(s)|²`. -/
theorem bcfMellinPlancherel : BCFMellinPlancherel :=
  bcfGramEnergy_eq_criticalLineEnergy

end

end NBMellinTools.H15BCF
