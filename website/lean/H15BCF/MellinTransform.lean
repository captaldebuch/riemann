/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.Definitions
import NBMellinTools.NB2BaseMellin

/-!
# Conditional BCF formalization: exact Mellin identity

This file proves the unconditional finite identity

`mellin (bcfApproximationError N) s =
  (1 - riemannZeta s * bcfDirichletPolynomial N s) / s`

on `0 < re s < 1`.  No Riemann-hypothesis assumption, contour shift, zero
sum, or asymptotic estimate is used.  The proof is finite Mellin linearity
together with `NB2.mellin_chi01` and `NB2.mellin_rhoBD`.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators
open MeasureTheory Set Complex
open NBMellinTools.NB2

private def rhoMellinIntegrand (k : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) * ((rhoBD k x : ℝ) : ℂ)

private theorem measurable_rhoBD (k : ℕ) : Measurable (rhoBD k) := by
  unfold rhoBD
  measurability

private theorem rho_mellin_integrableOn_Ioc01
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioc (0 : ℝ) 1) := by
  have hk := intervalIntegral.intervalIntegrable_cpow'
    (r := s - 1) (a := (0 : ℝ)) (b := 1) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hk
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => ((rhoBD k x : ℝ) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (measurable_rhoBD k).complex_ofReal.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖((rhoBD k x : ℝ) : ℂ)‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    unfold rhoBD
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hnon : 0 ≤ Int.fract (1 / (((k : ℝ) + 1) * x)) :=
      Int.fract_nonneg _
    rw [abs_of_nonneg hnon]
    exact (Int.fract_lt_one _).le
  have hmul := hk.mul_bdd hmeas hbound
  simpa [rhoMellinIntegrand, smul_eq_mul] using hmul

private theorem rho_mellin_integrableOn_Ioi_one
    {s : ℂ} (hs : s.re < 1) (k : ℕ) :
    IntegrableOn (rhoMellinIntegrand k s) (Ioi (1 : ℝ)) := by
  have hcpow : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 2)) (Ioi (1 : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt
    · change s.re - 2 < -1
      linarith
    · exact one_pos
  have hmodel : IntegrableOn
      (fun x : ℝ => (((k : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
        (x : ℂ) ^ (s - 2)) (Ioi (1 : ℝ)) :=
    hcpow.const_mul _
  apply hmodel.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hx))
  dsimp [rhoMellinIntegrand]
  rw [rhoBD_eq_one_div_of_one_lt k hx]
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  rw [show s - 2 = (s - 1) - 1 by ring,
    Complex.cpow_sub (s - 1) 1 hx0, Complex.cpow_one]
  field_simp
  simp

/-- Every Báez--Duarte generator has a convergent Mellin transform on the
open critical strip. -/
theorem rhoBD_mellinConvergent
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (k : ℕ) :
    MellinConvergent (fun x : ℝ => (rhoBD k x : ℂ)) s := by
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  simpa [rhoMellinIntegrand, smul_eq_mul] using
    (rho_mellin_integrableOn_Ioc01 hs0 k).union
      (rho_mellin_integrableOn_Ioi_one hs1 k)

/-- The existing exact generator evaluation, bundled with convergence. -/
theorem hasMellin_rhoBD
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (k : ℕ) :
    HasMellin (fun x : ℝ => (rhoBD k x : ℂ)) s
      (-(riemannZeta s) /
        (s * ((((k + 1 : ℕ) : ℝ) : ℂ) ^ s))) :=
  ⟨rhoBD_mellinConvergent hs0 hs1 k, mellin_rhoBD k hs0 hs1⟩

private theorem chi01_mellinConvergent
    {s : ℂ} (hs0 : 0 < s.re) :
    MellinConvergent (fun x : ℝ => (chi01 x : ℂ)) s := by
  simpa only [chi01_eq_indicator] using (hasMellin_one_Ioc hs0).1

/-- The finite BCF generator combination has a convergent Mellin transform
on the open critical strip. -/
theorem bcfApproximation_mellinConvergent
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (N : ℕ) :
    MellinConvergent (fun x : ℝ => (bcfApproximation N x : ℂ)) s := by
  unfold MellinConvergent bcfApproximation
  rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      (↑(∑ k : Fin N,
        bcfCoefficient N (k.val + 1) * rhoBD k.val x) : ℂ)) =
      (fun x : ℝ => ∑ k : Fin N,
        (x : ℂ) ^ (s - 1) *
          (bcfCoefficient N (k.val + 1) : ℂ) *
          (rhoBD k.val x : ℂ)) by
        funext x
        push_cast
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring]
  apply MeasureTheory.integrable_finsetSum (Finset.univ : Finset (Fin N))
  intro k hk
  have h := rhoBD_mellinConvergent hs0 hs1 k.val
  simpa [MellinConvergent, smul_eq_mul, mul_assoc, mul_left_comm,
    mul_comm] using h.const_smul (bcfCoefficient N (k.val + 1) : ℂ)

/-- Mellin transform of the finite BCF generator combination. -/
theorem mellin_bcfApproximation
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (N : ℕ) :
    mellin (fun x : ℝ => (bcfApproximation N x : ℂ)) s =
      (-(riemannZeta s) / s) * bcfDirichletPolynomial N s := by
  unfold mellin bcfApproximation
  rw [show (fun x : ℝ => (x : ℂ) ^ (s - 1) •
      (↑(∑ k : Fin N,
        bcfCoefficient N (k.val + 1) * rhoBD k.val x) : ℂ)) =
      (fun x : ℝ => ∑ k : Fin N,
        (x : ℂ) ^ (s - 1) *
          (bcfCoefficient N (k.val + 1) : ℂ) *
          (rhoBD k.val x : ℂ)) by
        funext x
        push_cast
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring]
  rw [MeasureTheory.integral_finsetSum]
  · unfold bcfDirichletPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (fun x : ℝ =>
        (x : ℂ) ^ (s - 1) *
          (bcfCoefficient N (k.val + 1) : ℂ) *
          (rhoBD k.val x : ℂ)) =
        (fun x : ℝ => (bcfCoefficient N (k.val + 1) : ℂ) *
          ((x : ℂ) ^ (s - 1) * (rhoBD k.val x : ℂ))) by
          funext x
          ring,
      MeasureTheory.integral_const_mul]
    change (bcfCoefficient N (k.val + 1) : ℂ) *
        mellin (fun x : ℝ => (rhoBD k.val x : ℂ)) s = _
    rw [mellin_rhoBD k.val hs0 hs1]
    push_cast
    ring
  · intro k hk
    have h := rhoBD_mellinConvergent hs0 hs1 k.val
    simpa [MellinConvergent, smul_eq_mul, mul_assoc, mul_left_comm,
      mul_comm] using h.const_smul (bcfCoefficient N (k.val + 1) : ℂ)

/-- The finite BCF error has a convergent Mellin transform on the open
critical strip. -/
theorem bcfApproximationError_mellinConvergent
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (N : ℕ) :
    MellinConvergent
      (fun x : ℝ => (bcfApproximationError N x : ℂ)) s := by
  have h := (hasMellin_add (chi01_mellinConvergent hs0)
    (bcfApproximation_mellinConvergent hs0 hs1 N)).1
  simpa [bcfApproximationError, Complex.ofReal_add] using h

/-- Exact BCF Mellin identity on `0 < re s < 1`.

This is equation (6) in `H15_CENTERED_ESTERMANN_THEOREM_MATCH.md`. -/
theorem bcfMellinTransform
    (N : ℕ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun x : ℝ => (bcfApproximationError N x : ℂ)) s =
      (1 - riemannZeta s * bcfDirichletPolynomial N s) / s := by
  have hlin := (hasMellin_add (chi01_mellinConvergent hs0)
    (bcfApproximation_mellinConvergent hs0 hs1 N)).2
  have hfun :
      (fun x : ℝ => (bcfApproximationError N x : ℂ)) =
      (fun x : ℝ => (chi01 x : ℂ) + (bcfApproximation N x : ℂ)) := by
    funext x
    simp [bcfApproximationError]
  rw [hfun, hlin, mellin_chi01 hs0,
    mellin_bcfApproximation hs0 hs1 N]
  ring

end

end NBMellinTools.H15BCF
