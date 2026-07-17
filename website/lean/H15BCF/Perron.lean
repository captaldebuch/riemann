/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.NumberTheory.LSeries.Dirichlet
import NBMellinTools.H15BCF.ContourShift

/-!
# Conditional BCF formalization: Perron starting line

This file formalizes the absolutely convergent algebra on the initial Perron
line in BCF Lemma 2.  In the half-plane `1 < re z`, the reciprocal of zeta is
exactly the Möbius Dirichlet series.  Substitution gives the series form of
the BCF Perron kernel on `re w = 2` whenever `0 < re s`.

The remaining analytic step is the inverse-Perron kernel identity for
`1 / w^2`, followed by justified interchange with this absolutely convergent
Dirichlet series.  It is deliberately not postulated here.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Lemma 2.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped ArithmeticFunction.Moebius LSeries.notation Topology
open Complex
open Filter

/-- On its half-plane of absolute convergence, `1 / zeta` is the Dirichlet
series of the Möbius function. -/
theorem bcf_inv_riemannZeta_eq_moebiusLSeries
    {z : ℂ} (hz : 1 < z.re) :
    (riemannZeta z)⁻¹ = L ↗μ z := by
  have hproduct := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hz
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz] at hproduct
  exact inv_eq_of_mul_eq_one_right hproduct

/-- On the initial Perron line, the BCF kernel is the Möbius Dirichlet series
times the elementary factor `N^w / w^2`. -/
theorem bcfPerronKernel_eq_moebiusLSeries
    (N : ℕ) {s w : ℂ} (hsw : 1 < (s + w).re) :
    bcfPerronKernel N s w =
      bcfNPow N w * (L ↗μ (s + w)) / w ^ 2 := by
  rw [bcfPerronKernel, div_eq_mul_inv, mul_inv_rev,
    bcf_inv_riemannZeta_eq_moebiusLSeries hsw]
  ring

/-- For `0 < re s`, every point `2 + it` of the initial BCF Perron contour
lies in the half-plane where the Möbius Dirichlet series for `1 / zeta`
converges absolutely. -/
theorem one_lt_re_add_two_vertical
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    1 < (s + ((2 : ℂ) + (t : ℂ) * I)).re := by
  rw [Complex.add_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  linarith

/-- The starting-line BCF kernel in Möbius-series form. -/
theorem bcfPerronKernel_initialLine_eq_moebiusLSeries
    (N : ℕ) {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    bcfPerronKernel N s ((2 : ℂ) + (t : ℂ) * I) =
      bcfNPow N ((2 : ℂ) + (t : ℂ) * I) *
        (L ↗μ (s + ((2 : ℂ) + (t : ℂ) * I))) /
          ((2 : ℂ) + (t : ℂ) * I) ^ 2 :=
  bcfPerronKernel_eq_moebiusLSeries N (one_lt_re_add_two_vertical hs t)

/-- The Möbius Dirichlet series appearing on the initial BCF Perron contour
is absolutely convergent at every height. -/
theorem bcf_moebiusLSeriesSummable_initialLine
    {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    LSeriesSummable ↗μ (s + ((2 : ℂ) + (t : ℂ) * I)) :=
  ArithmeticFunction.LSeriesSummable_moebius_iff.mpr
    (one_lt_re_add_two_vertical hs t)

/-- A truncated initial BCF vertical integral can be rewritten pointwise as
an integral of the absolutely convergent Möbius Dirichlet series.  This is
only a finite-interval substitution: the later termwise improper integration
still needs a uniform domination argument. -/
theorem bcfTruncatedVerticalIntegral_eq_moebiusLSeries
    (N : ℕ) {s : ℂ} (hs : 0 < s.re) (T : ℝ) :
    bcfTruncatedVerticalIntegral N s 2 T =
      ∫ t in (-T)..T,
        (bcfNPow N ((2 : ℂ) + (t : ℂ) * I) *
          L ↗μ (s + ((2 : ℂ) + (t : ℂ) * I)) /
            ((2 : ℂ) + (t : ℂ) * I) ^ 2) * I := by
  unfold bcfTruncatedVerticalIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change
    bcfPerronKernel N s ((2 : ℂ) + (t : ℂ) * I) * I =
      (bcfNPow N ((2 : ℂ) + (t : ℂ) * I) *
        L ↗μ (s + ((2 : ℂ) + (t : ℂ) * I)) /
          ((2 : ℂ) + (t : ℂ) * I) ^ 2) * I
  rw [bcfPerronKernel_initialLine_eq_moebiusLSeries N hs t]

/-- The derivative at zero of the holomorphic numerator in the Perron kernel.
It is the coefficient of `w⁻¹` in `N^w / w^2`. -/
theorem deriv_bcfNPow_zero
    (N : ℕ) :
    deriv (bcfNPow N) 0 = (Real.log N : ℂ) := by
  unfold bcfNPow
  calc
    deriv (fun z : ℂ => (N : ℂ) ^ z) 0 =
        Complex.log (N : ℂ) * deriv (fun z : ℂ => z) 0 * (N : ℂ) ^ (0 : ℂ) := by
      simpa using Complex.deriv_const_cpow
        (f := fun z : ℂ => z) (x := (0 : ℂ)) differentiableAt_id (N : ℂ)
    _ = (Real.log N : ℂ) := by
      simp only [deriv_id'', mul_one, Complex.cpow_zero]
      exact (Complex.ofReal_log (Nat.cast_nonneg N)).symm

/-- The closed-contour contribution of the order-two Perron kernel.

This is a residue calculation, not the inverse-Perron step: the integral is
`2πi log N`.  The piecewise `log x`/`0` value arises only after taking an
improper vertical-line integral. -/
theorem circleIntegral_bcfNPow_div_sq
    {N : ℕ} (hN : N ≠ 0) {R : ℝ} (hR : 0 < R) :
    (∮ w in C(0, R), bcfNPow N w / w ^ 2) =
      2 * Real.pi * I * (Real.log N : ℂ) := by
  have hdiff : DifferentiableOn ℂ (bcfNPow N) (Metric.closedBall 0 R) := by
    intro z _
    unfold bcfNPow
    exact (differentiableAt_id.const_cpow
      (Or.inl (show (N : ℂ) ≠ 0 by exact_mod_cast hN))).differentiableWithinAt
  calc
    (∮ w in C(0, R), bcfNPow N w / w ^ 2) =
        ∮ w in C(0, R), (1 / (w - 0) ^ 2) • bcfNPow N w := by
      apply circleIntegral.integral_congr hR.le
      intro w _
      change bcfNPow N w / w ^ 2 = (1 / (w - 0) ^ 2) • bcfNPow N w
      rw [div_eq_mul_inv]
      simp only [smul_eq_mul, sub_zero]
      ring
    _ = (2 * Real.pi * I) • deriv (bcfNPow N) 0 :=
      hdiff.deriv_eq_smul_circleIntegral hR
    _ = 2 * Real.pi * I * (Real.log N : ℂ) := by
      rw [deriv_bcfNPow_zero N]
      simp [smul_eq_mul]

/-- The left semicircular boundary arc for the elementary inverse-Perron
kernel `N^w / w^2`, parametrized counterclockwise from `iR` to `-iR`. -/
def bcfLeftPerronArcIntegral (N : ℕ) (R : ℝ) : ℂ :=
  ∫ theta in (Real.pi / 2)..(Real.pi + Real.pi / 2),
    bcfNPow N (circleMap 0 R theta) / (circleMap 0 R theta) ^ 2 *
      deriv (circleMap 0 R) theta

private theorem norm_bcfNPow_circleMap_left_le_one
    {N : ℕ} {R theta : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R)
    (htheta_lower : Real.pi / 2 ≤ theta)
    (htheta_upper : theta ≤ Real.pi + Real.pi / 2) :
    ‖bcfNPow N (circleMap 0 R theta)‖ ≤ 1 := by
  unfold bcfNPow
  rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hN)]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast hN
  · rw [circleMap_zero_re]
    exact mul_nonpos_of_nonneg_of_nonpos hR
      (Real.cos_nonpos_of_pi_div_two_le_of_le htheta_lower htheta_upper)

private theorem norm_bcfLeftPerronArcIntegrand_le
    {N : ℕ} {R theta : ℝ} (hN : 1 ≤ N) (hR : 0 < R)
    (htheta_lower : Real.pi / 2 ≤ theta)
    (htheta_upper : theta ≤ Real.pi + Real.pi / 2) :
    ‖bcfNPow N (circleMap 0 R theta) / (circleMap 0 R theta) ^ 2 *
        deriv (circleMap 0 R) theta‖ ≤ 1 / R := by
  have hnum := norm_bcfNPow_circleMap_left_le_one hN hR.le
    htheta_lower htheta_upper
  have hcircle : ‖circleMap 0 R theta‖ = R := by
    rw [norm_circleMap_zero, abs_of_pos hR]
  calc
    ‖bcfNPow N (circleMap 0 R theta) / (circleMap 0 R theta) ^ 2 *
        deriv (circleMap 0 R) theta‖ =
        ‖bcfNPow N (circleMap 0 R theta)‖ /
          ‖(circleMap 0 R theta) ^ 2‖ * ‖deriv (circleMap 0 R) theta‖ := by
      rw [norm_mul, norm_div]
    _ = ‖bcfNPow N (circleMap 0 R theta)‖ / R ^ 2 * R := by
      rw [norm_pow, hcircle, deriv_circleMap, norm_mul, hcircle, norm_I, mul_one]
    _ ≤ 1 / R ^ 2 * R := by gcongr
    _ = 1 / R := by field_simp

/-- The left boundary arc is `O(1/R)` when `N ≥ 1`.  This is the elementary
arc estimate required when closing the inverse-Perron contour to the left. -/
theorem norm_bcfLeftPerronArcIntegral_le
    {N : ℕ} {R : ℝ} (hN : 1 ≤ N) (hR : 0 < R) :
    ‖bcfLeftPerronArcIntegral N R‖ ≤ Real.pi / R := by
  unfold bcfLeftPerronArcIntegral
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1 / R) ?_).trans_eq ?_
  · intro theta htheta
    have hangle : Real.pi / 2 ≤ Real.pi + Real.pi / 2 := by
      linarith [Real.pi_pos]
    rw [Set.uIoc_of_le hangle] at htheta
    exact norm_bcfLeftPerronArcIntegrand_le hN hR htheta.1.le htheta.2
  · rw [show (Real.pi + Real.pi / 2) - Real.pi / 2 = Real.pi by ring,
      abs_of_nonneg Real.pi_pos.le]
    ring

/-- The left boundary arc of the elementary inverse-Perron kernel vanishes
as its radius tends to infinity. -/
theorem tendsto_bcfLeftPerronArcIntegral_atTop
    {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun R : ℝ => bcfLeftPerronArcIntegral N R) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_bcfLeftPerronArcIntegral_le hN hR
  · simpa only [div_eq_mul_inv] using
      (show Tendsto (fun R : ℝ => Real.pi * R⁻¹) atTop (𝓝 0) from
        by
          have hconst : Tendsto (fun _ : ℝ => Real.pi) atTop (𝓝 Real.pi) :=
            tendsto_const_nhds
          simpa using hconst.mul (tendsto_inv_atTop_zero :
            Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0)))

/-- The left semicircular boundary arc centred at the initial Perron line
`re w = 2`.  Together with the vertical segment from `2 + iR` to `2 - iR`,
this is the actual contour used to close the elementary kernel to the left. -/
def bcfInitialLineLeftArcIntegral (N : ℕ) (R : ℝ) : ℂ :=
  ∫ theta in (Real.pi / 2)..(Real.pi + Real.pi / 2),
    bcfNPow N ((2 : ℂ) + circleMap 0 R theta) /
        ((2 : ℂ) + circleMap 0 R theta) ^ 2 *
      deriv (circleMap 0 R) theta

private theorem norm_bcfNPow_of_re_le_two
    {N : ℕ} {w : ℂ} (hN : 1 ≤ N) (hw : w.re ≤ 2) :
    ‖bcfNPow N w‖ ≤ (N : ℝ) ^ (2 : ℝ) := by
  unfold bcfNPow
  rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hN)]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hN
  · exact hw

private theorem norm_bcfNPow_initialLineLeft_le
    {N : ℕ} {R theta : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R)
    (htheta_lower : Real.pi / 2 ≤ theta)
    (htheta_upper : theta ≤ Real.pi + Real.pi / 2) :
    ‖bcfNPow N ((2 : ℂ) + circleMap 0 R theta)‖ ≤
      (N : ℝ) ^ (2 : ℝ) := by
  apply norm_bcfNPow_of_re_le_two hN
  rw [Complex.add_re, circleMap_zero_re]
  have hcos : R * Real.cos theta ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hR
      (Real.cos_nonpos_of_pi_div_two_le_of_le htheta_lower htheta_upper)
  norm_num
  linarith

private theorem initialLineLeft_norm_lower
    {R theta : ℝ} (hR : 0 < R) :
    R - 2 ≤ ‖(2 : ℂ) + circleMap 0 R theta‖ := by
  have h := norm_sub_norm_le (circleMap 0 R theta) (-(2 : ℂ))
  rw [norm_circleMap_zero, abs_of_pos hR, norm_neg] at h
  norm_num at h
  have h' : R - 2 ≤ ‖circleMap 0 R theta + (2 : ℂ)‖ := by linarith
  simpa [add_comm] using h'

private theorem norm_bcfInitialLineLeftArcIntegrand_le
    {N : ℕ} {R theta : ℝ} (hN : 1 ≤ N) (hR : 2 < R)
    (htheta_lower : Real.pi / 2 ≤ theta)
    (htheta_upper : theta ≤ Real.pi + Real.pi / 2) :
    ‖bcfNPow N ((2 : ℂ) + circleMap 0 R theta) /
        ((2 : ℂ) + circleMap 0 R theta) ^ 2 *
      deriv (circleMap 0 R) theta‖ ≤
      (N : ℝ) ^ (2 : ℝ) * R / (R - 2) ^ 2 := by
  have hnum := norm_bcfNPow_initialLineLeft_le hN (by linarith : 0 ≤ R)
    htheta_lower htheta_upper
  have hgap : 0 < R - 2 := by linarith
  have hden := initialLineLeft_norm_lower (theta := theta) (by linarith : 0 < R)
  have hden_sq : (R - 2) ^ 2 ≤ ‖(2 : ℂ) + circleMap 0 R theta‖ ^ 2 := by
    exact (sq_le_sq₀ hgap.le (norm_nonneg _)).mpr hden
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ (2 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    ‖bcfNPow N ((2 : ℂ) + circleMap 0 R theta) /
        ((2 : ℂ) + circleMap 0 R theta) ^ 2 *
      deriv (circleMap 0 R) theta‖ =
        ‖bcfNPow N ((2 : ℂ) + circleMap 0 R theta)‖ /
          ‖(2 : ℂ) + circleMap 0 R theta‖ ^ 2 *
            ‖deriv (circleMap 0 R) theta‖ := by
      rw [norm_mul, norm_div, norm_pow]
    _ = ‖bcfNPow N ((2 : ℂ) + circleMap 0 R theta)‖ /
          ‖(2 : ℂ) + circleMap 0 R theta‖ ^ 2 * R := by
      rw [deriv_circleMap, norm_mul, norm_circleMap_zero, abs_of_pos (by linarith : 0 < R),
        norm_I, mul_one]
    _ ≤ ((N : ℝ) ^ (2 : ℝ) /
          ‖(2 : ℂ) + circleMap 0 R theta‖ ^ 2) * R := by
      gcongr
    _ ≤ ((N : ℝ) ^ (2 : ℝ) / (R - 2) ^ 2) * R := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact div_le_div_of_nonneg_left hpow_nonneg (sq_pos_of_pos hgap) hden_sq
    _ = (N : ℝ) ^ (2 : ℝ) * R / (R - 2) ^ 2 := by ring

/-- The left boundary arc closing the initial line `re w = 2` is bounded by
`π N² R / (R - 2)²`.  Unlike the arc centred at zero, this is compatible with
the original Perron segment. -/
theorem norm_bcfInitialLineLeftArcIntegral_le
    {N : ℕ} {R : ℝ} (hN : 1 ≤ N) (hR : 2 < R) :
    ‖bcfInitialLineLeftArcIntegral N R‖ ≤
      Real.pi * (N : ℝ) ^ (2 : ℝ) * R / (R - 2) ^ 2 := by
  unfold bcfInitialLineLeftArcIntegral
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (N : ℝ) ^ (2 : ℝ) * R / (R - 2) ^ 2) ?_).trans_eq ?_
  · intro theta htheta
    have hangle : Real.pi / 2 ≤ Real.pi + Real.pi / 2 := by
      linarith [Real.pi_pos]
    rw [Set.uIoc_of_le hangle] at htheta
    exact norm_bcfInitialLineLeftArcIntegrand_le hN hR htheta.1.le htheta.2
  · rw [show (Real.pi + Real.pi / 2) - Real.pi / 2 = Real.pi by ring,
      abs_of_nonneg Real.pi_pos.le]
    ring

/-- The shifted left boundary arc tends to zero as its radius tends to
infinity.  The proof uses the eventual comparison `R - 2 ≥ R / 2`. -/
theorem tendsto_bcfInitialLineLeftArcIntegral_atTop
    {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun R : ℝ => bcfInitialLineLeftArcIntegral N R) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with R hR
    have hR' : 2 < R := by linarith
    calc
      ‖bcfInitialLineLeftArcIntegral N R‖ ≤
          Real.pi * (N : ℝ) ^ (2 : ℝ) * R / (R - 2) ^ 2 :=
        norm_bcfInitialLineLeftArcIntegral_le hN hR'
      _ ≤ (4 * Real.pi * (N : ℝ) ^ (2 : ℝ)) / R := by
        have hhalf : R / 2 ≤ R - 2 := by linarith
        have hsquare : (R / 2) ^ 2 ≤ (R - 2) ^ 2 := by
          exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hhalf
        calc
          Real.pi * (N : ℝ) ^ (2 : ℝ) * R / (R - 2) ^ 2 ≤
              Real.pi * (N : ℝ) ^ (2 : ℝ) * R / (R / 2) ^ 2 := by
            exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (by positivity)) hsquare
          _ = (4 * Real.pi * (N : ℝ) ^ (2 : ℝ)) / R := by
            field_simp
            norm_num
  · have hconst : Tendsto (fun _ : ℝ =>
        4 * Real.pi * (N : ℝ) ^ (2 : ℝ)) atTop
        (𝓝 (4 * Real.pi * (N : ℝ) ^ (2 : ℝ))) := tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hconst.mul
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))

/-- The horizontal edge of the elementary Perron rectangle at height `t`,
oriented from `-a + it` to `2 + it`. -/
def bcfHorizontalPerronEdgeIntegral (N : ℕ) (a t : ℝ) : ℂ :=
  ∫ x in (-a)..2,
    bcfNPow N ((x : ℂ) + (t : ℂ) * I) /
      ((x : ℂ) + (t : ℂ) * I) ^ 2

private theorem abs_im_le_norm_horizontalPerronPoint (x t : ℝ) :
    |t| ≤ ‖(x : ℂ) + (t : ℂ) * I‖ := by
  simpa using (abs_im_le_norm ((x : ℂ) + (t : ℂ) * I))

private theorem norm_bcfHorizontalPerronIntegrand_le
    {N : ℕ} {x t : ℝ} (hN : 1 ≤ N) (ht : t ≠ 0) (hx : x ≤ 2) :
    ‖bcfNPow N ((x : ℂ) + (t : ℂ) * I) /
        ((x : ℂ) + (t : ℂ) * I) ^ 2‖ ≤
      (N : ℝ) ^ (2 : ℝ) / |t| ^ 2 := by
  have hnum : ‖bcfNPow N ((x : ℂ) + (t : ℂ) * I)‖ ≤
      (N : ℝ) ^ (2 : ℝ) := by
    apply norm_bcfNPow_of_re_le_two hN
    simpa using hx
  have habs : 0 < |t| := abs_pos.mpr ht
  have hden := abs_im_le_norm_horizontalPerronPoint x t
  have hden_sq : |t| ^ 2 ≤ ‖(x : ℂ) + (t : ℂ) * I‖ ^ 2 :=
    (sq_le_sq₀ habs.le (norm_nonneg _)).mpr hden
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ (2 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    ‖bcfNPow N ((x : ℂ) + (t : ℂ) * I) /
        ((x : ℂ) + (t : ℂ) * I) ^ 2‖ =
        ‖bcfNPow N ((x : ℂ) + (t : ℂ) * I)‖ /
          ‖(x : ℂ) + (t : ℂ) * I‖ ^ 2 := by
      rw [norm_div, norm_pow]
    _ ≤ (N : ℝ) ^ (2 : ℝ) /
          ‖(x : ℂ) + (t : ℂ) * I‖ ^ 2 := by
      gcongr
    _ ≤ (N : ℝ) ^ (2 : ℝ) / |t| ^ 2 := by
      exact div_le_div_of_nonneg_left hpow_nonneg (sq_pos_of_pos habs) hden_sq

/-- Each horizontal edge of the elementary Perron rectangle has an explicit
`O(T⁻²)` bound.  This controls the upper and lower edges after setting
`t = T` and `t = -T`, respectively. -/
theorem norm_bcfHorizontalPerronEdgeIntegral_le
    {N : ℕ} {a t : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) (ht : t ≠ 0) :
    ‖bcfHorizontalPerronEdgeIntegral N a t‖ ≤
      (a + 2) * (N : ℝ) ^ (2 : ℝ) / |t| ^ 2 := by
  unfold bcfHorizontalPerronEdgeIntegral
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (N : ℝ) ^ (2 : ℝ) / |t| ^ 2) ?_).trans_eq ?_
  · intro x hx
    have hinterval : -a ≤ 2 := by linarith
    rw [Set.uIoc_of_le hinterval] at hx
    exact norm_bcfHorizontalPerronIntegrand_le hN ht hx.2
  · have hlength : |2 - -a| = a + 2 := by
      rw [show 2 - -a = a + 2 by ring]
      exact abs_of_nonneg (by linarith)
    rw [hlength]
    ring

/-- The upper horizontal edge of the elementary Perron rectangle tends to
zero as its height tends to infinity. -/
theorem tendsto_bcfHorizontalPerronEdgeIntegral_atTop
    {N : ℕ} {a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    Tendsto (fun T : ℝ => bcfHorizontalPerronEdgeIntegral N a T) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    calc
      ‖bcfHorizontalPerronEdgeIntegral N a T‖ ≤
          (a + 2) * (N : ℝ) ^ (2 : ℝ) / |T| ^ 2 :=
        norm_bcfHorizontalPerronEdgeIntegral_le hN ha hT.ne'
      _ = (a + 2) * (N : ℝ) ^ (2 : ℝ) / T ^ 2 := by
        rw [abs_of_pos hT]
  · have hconst : Tendsto (fun _ : ℝ =>
        (a + 2) * (N : ℝ) ^ (2 : ℝ)) atTop
        (𝓝 ((a + 2) * (N : ℝ) ^ (2 : ℝ))) := tendsto_const_nhds
    simpa [div_eq_mul_inv, inv_pow] using hconst.mul
      ((tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).pow 2)

/-- The lower horizontal edge has the same vanishing limit, with `t = -T`. -/
theorem tendsto_bcfHorizontalPerronEdgeIntegral_neg_atTop
    {N : ℕ} {a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    Tendsto (fun T : ℝ => bcfHorizontalPerronEdgeIntegral N a (-T)) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    calc
      ‖bcfHorizontalPerronEdgeIntegral N a (-T)‖ ≤
          (a + 2) * (N : ℝ) ^ (2 : ℝ) / |-T| ^ 2 :=
        norm_bcfHorizontalPerronEdgeIntegral_le hN ha (neg_ne_zero.mpr hT.ne')
      _ = (a + 2) * (N : ℝ) ^ (2 : ℝ) / T ^ 2 := by
        rw [abs_neg, abs_of_pos hT]
  · have hconst : Tendsto (fun _ : ℝ =>
        (a + 2) * (N : ℝ) ^ (2 : ℝ)) atTop
        (𝓝 ((a + 2) * (N : ℝ) ^ (2 : ℝ))) := tendsto_const_nhds
    simpa [div_eq_mul_inv, inv_pow] using hconst.mul
      ((tendsto_inv_atTop_zero : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0)).pow 2)

/-- The full BCF kernel is the elementary Perron kernel multiplied by the
reciprocal-zeta factor.  This algebraic form is used to attach contour bounds
for `1 / ζ(s + w)` without hiding any zero-free hypothesis. -/
theorem bcfPerronKernel_eq_elementary_mul_invZeta
    (N : ℕ) (s w : ℂ) :
    bcfPerronKernel N s w =
      (bcfNPow N w / w ^ 2) * (riemannZeta (s + w))⁻¹ := by
  rw [bcfPerronKernel, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The horizontal edge of the full BCF Perron kernel.  Unlike
`bcfHorizontalPerronEdgeIntegral`, this includes the reciprocal-zeta factor
and therefore needs an explicit zero-free contour bound. -/
def bcfFullHorizontalPerronEdgeIntegral
    (N : ℕ) (s : ℂ) (a t : ℝ) : ℂ :=
  ∫ x in (-a)..2,
    bcfPerronKernel N s ((x : ℂ) + (t : ℂ) * I)

/-- Data certifying that a horizontal edge avoids zeta zeros and has a uniform
bound on `1 / ζ`.  The nonvanishing field is essential: Lean totalizes inverse
at zero, whereas the meromorphic Perron kernel has a pole there. -/
structure BCFHorizontalReciprocalZetaBound (s : ℂ) (a t B : ℝ) : Prop where
  zero_free : ∀ x : ℝ, -a ≤ x → x ≤ 2 →
    riemannZeta (s + ((x : ℂ) + (t : ℂ) * I)) ≠ 0
  inv_bound : ∀ x : ℝ, -a ≤ x → x ≤ 2 →
    ‖(riemannZeta (s + ((x : ℂ) + (t : ℂ) * I)))⁻¹‖ ≤ B

/-- A reciprocal-zeta bound on a single horizontal edge transfers the
elementary `O(T⁻²)` estimate to the full BCF kernel.  The hypothesis is
deliberately local: it must be established on a zero-free edge, or on each
component after deleting disks around zeta zeros. -/
theorem norm_bcfFullHorizontalPerronEdgeIntegral_le
    {N : ℕ} {s : ℂ} {a t B : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) (ht : t ≠ 0)
    (hcontour : BCFHorizontalReciprocalZetaBound s a t B) :
    ‖bcfFullHorizontalPerronEdgeIntegral N s a t‖ ≤
      (a + 2) * (N : ℝ) ^ (2 : ℝ) * B / |t| ^ 2 := by
  unfold bcfFullHorizontalPerronEdgeIntegral
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (N : ℝ) ^ (2 : ℝ) * B / |t| ^ 2) ?_).trans_eq ?_
  · intro x hx
    have hinterval : -a ≤ 2 := by linarith
    rw [Set.uIoc_of_le hinterval] at hx
    have helementary := norm_bcfHorizontalPerronIntegrand_le hN ht hx.2
    have hfactor := hcontour.inv_bound x hx.1.le hx.2
    have helementary_nonneg :
        0 ≤ (N : ℝ) ^ (2 : ℝ) / |t| ^ 2 := by positivity
    calc
      ‖bcfPerronKernel N s ((x : ℂ) + (t : ℂ) * I)‖ =
          ‖bcfNPow N ((x : ℂ) + (t : ℂ) * I) /
              ((x : ℂ) + (t : ℂ) * I) ^ 2‖ *
            ‖(riemannZeta (s + ((x : ℂ) + (t : ℂ) * I)))⁻¹‖ := by
        rw [bcfPerronKernel_eq_elementary_mul_invZeta, norm_mul]
      _ ≤ ((N : ℝ) ^ (2 : ℝ) / |t| ^ 2) * B := by
        exact mul_le_mul helementary hfactor (norm_nonneg _) helementary_nonneg
      _ = (N : ℝ) ^ (2 : ℝ) * B / |t| ^ 2 := by ring
  · have hlength : |2 - -a| = a + 2 := by
      rw [show 2 - -a = a + 2 by ring]
      exact abs_of_nonneg (by linarith)
    rw [hlength]
    ring

/-- An asymptotically small reciprocal-zeta envelope for the two horizontal
edges of a Perron rectangle.  The required decay is exactly what remains after
the elementary factor contributes `T⁻²`. -/
structure BCFHorizontalReciprocalZetaControl (s : ℂ) (a : ℝ) where
  envelope : ℝ → ℝ
  top : ∀ T : ℝ, 0 < T →
    BCFHorizontalReciprocalZetaBound s a T (envelope T)
  bottom : ∀ T : ℝ, 0 < T →
    BCFHorizontalReciprocalZetaBound s a (-T) (envelope T)
  decay : Tendsto (fun T : ℝ => envelope T / T ^ 2) atTop (𝓝 0)

/-- Under a genuine reciprocal-zeta contour control, the upper horizontal
edge of the full BCF kernel vanishes. -/
theorem tendsto_bcfFullHorizontalPerronEdgeIntegral_atTop
    {N : ℕ} {s : ℂ} {a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hcontrol : BCFHorizontalReciprocalZetaControl s a) :
    Tendsto (fun T : ℝ => bcfFullHorizontalPerronEdgeIntegral N s a T)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    calc
      ‖bcfFullHorizontalPerronEdgeIntegral N s a T‖ ≤
          (a + 2) * (N : ℝ) ^ (2 : ℝ) * hcontrol.envelope T / |T| ^ 2 :=
        norm_bcfFullHorizontalPerronEdgeIntegral_le hN ha hT.ne'
          (hcontrol.top T hT)
      _ = ((a + 2) * (N : ℝ) ^ (2 : ℝ)) *
          (hcontrol.envelope T / T ^ 2) := by
        rw [abs_of_pos hT]
        ring
  · have hconst : Tendsto (fun _ : ℝ =>
        (a + 2) * (N : ℝ) ^ (2 : ℝ)) atTop
        (𝓝 ((a + 2) * (N : ℝ) ^ (2 : ℝ))) := tendsto_const_nhds
    simpa using hconst.mul hcontrol.decay

/-- The same contour control makes the lower horizontal edge vanish. -/
theorem tendsto_bcfFullHorizontalPerronEdgeIntegral_neg_atTop
    {N : ℕ} {s : ℂ} {a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hcontrol : BCFHorizontalReciprocalZetaControl s a) :
    Tendsto (fun T : ℝ => bcfFullHorizontalPerronEdgeIntegral N s a (-T))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    calc
      ‖bcfFullHorizontalPerronEdgeIntegral N s a (-T)‖ ≤
          (a + 2) * (N : ℝ) ^ (2 : ℝ) * hcontrol.envelope T / |-T| ^ 2 :=
        norm_bcfFullHorizontalPerronEdgeIntegral_le hN ha
          (neg_ne_zero.mpr hT.ne') (hcontrol.bottom T hT)
      _ = ((a + 2) * (N : ℝ) ^ (2 : ℝ)) *
          (hcontrol.envelope T / T ^ 2) := by
        rw [abs_neg, abs_of_pos hT]
        ring
  · have hconst : Tendsto (fun _ : ℝ =>
        (a + 2) * (N : ℝ) ^ (2 : ℝ)) atTop
        (𝓝 ((a + 2) * (N : ℝ) ^ (2 : ℝ))) := tendsto_const_nhds
    simpa using hconst.mul hcontrol.decay

end

end NBMellinTools.H15BCF
