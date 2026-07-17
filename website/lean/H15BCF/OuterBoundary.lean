/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.DeletedDiskAssembly
import NBMellinTools.H15BCF.Perron

/-!
# Conditional BCF formalization: outer-boundary bookkeeping

This file records the finite contribution of the order-two pole of the
shifted Perron kernel at `z = s`.  The deleted disks constructed in
`DeletedDiskAssembly` handle the nontrivial-zero poles; the circle below is
the remaining local term which becomes the BCF main term after Perron
normalization.

The genuinely global part of the contour shift remains separate: a rectangle
with these disks deleted must be decomposed into its outer boundary and the
oriented circle boundaries, and its outer pieces must be estimated.  The
theorems here do not postulate that deformation.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Metric Set

/-- The holomorphic numerator at the double pole `z = s` of the shifted BCF
kernel. -/
def bcfShiftedMainNumerator (N : ℕ) (s z : ℂ) : ℂ :=
  bcfNPow N (z - s) / riemannZeta z

/-- Factoring the shifted kernel into its holomorphic numerator and the
double-pole factor. -/
theorem bcfShiftedZeroKernel_eq_mainNumerator_div_sq
    (N : ℕ) (s z : ℂ) :
    bcfShiftedZeroKernel N s z =
      bcfShiftedMainNumerator N s z / (z - s) ^ 2 := by
  simp only [bcfShiftedZeroKernel, bcfShiftedMainNumerator]
  rw [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The derivative of the holomorphic numerator at the shifted double pole.
This is the order-one Laurent coefficient of the BCF kernel at `z = s`. -/
theorem hasDerivAt_bcfShiftedMainNumerator
    {N : ℕ} {s : ℂ} (hN : N ≠ 0)
    (hs_one : s ≠ 1) (hs_zero : riemannZeta s ≠ 0) :
    HasDerivAt (bcfShiftedMainNumerator N s)
      ((Real.log N : ℂ) / riemannZeta s -
        deriv riemannZeta s / (riemannZeta s) ^ 2) s := by
  have hpow : HasDerivAt (fun z : ℂ => bcfNPow N (z - s))
      (Real.log N : ℂ) s := by
    unfold bcfNPow
    have hsub : HasDerivAt (fun z : ℂ => z - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    rw [Complex.ofReal_log (Nat.cast_nonneg N)]
    simpa only [sub_self, Complex.cpow_zero, one_mul, smul_eq_mul,
      mul_one] using
      hsub.const_cpow (c := (N : ℂ))
        (Or.inl (show (N : ℂ) ≠ 0 by exact_mod_cast hN))
  have hzeta : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs_one).hasDerivAt
  change HasDerivAt ((fun z : ℂ => bcfNPow N (z - s)) / riemannZeta)
    ((Real.log N : ℂ) / riemannZeta s -
      deriv riemannZeta s / (riemannZeta s) ^ 2) s
  convert hpow.div hzeta hs_zero using 1
  simp only [bcfNPow, sub_self, Complex.cpow_zero, one_mul,
    Complex.ofReal_log (Nat.cast_nonneg N)]
  field_simp

/-- On a closed disk about `s` avoiding the zeta pole and zeta zeros, the
numerator of the shifted kernel is holomorphic. -/
theorem differentiableOn_bcfShiftedMainNumerator
    {N : ℕ} {s : ℂ} {R : ℝ} (hN : N ≠ 0)
    (hone : ∀ z ∈ closedBall s R, z ≠ 1)
    (hzero : ∀ z ∈ closedBall s R, riemannZeta z ≠ 0) :
    DifferentiableOn ℂ (bcfShiftedMainNumerator N s) (closedBall s R) := by
  intro z hz
  unfold bcfShiftedMainNumerator bcfNPow
  exact ((differentiableAt_id.sub_const s).const_cpow
    (Or.inl (show (N : ℂ) ≠ 0 by exact_mod_cast hN))).div
      (differentiableAt_riemannZeta (hone z hz)) (hzero z hz)
        |>.differentiableWithinAt

/-- A regular point of zeta different from `1` has a positive closed disk
free of both exceptional sets.  Thus the local circle used for the double
pole can always be chosen before the deleted-rectangle construction begins. -/
theorem exists_bcfShiftedMainPoleRadius
    {s : ℂ} (hs_one : s ≠ 1) (hs_zero : riemannZeta s ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ closedBall s R, z ≠ 1) ∧
      (∀ z ∈ closedBall s R, riemannZeta z ≠ 0) := by
  have hopen : IsOpen ({1}ᶜ ∩ riemannZetaZerosᶜ : Set ℂ) :=
    (isOpen_compl_iff.mpr isClosed_singleton).inter
      (isOpen_compl_iff.mpr isClosed_riemannZetaZeros)
  have hs_mem : s ∈ ({1}ᶜ ∩ riemannZetaZerosᶜ : Set ℂ) := by
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff,
      mem_riemannZetaZeros]
    exact ⟨hs_one, hs_zero⟩
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hopen s hs_mem
  refine ⟨r / 2, half_pos hr_pos, ?_, ?_⟩
  · intro z hz
    have hzball : z ∈ ball s r :=
      closedBall_subset_ball (half_lt_self hr_pos) hz
    have hzgood := hr_ball hzball
    simpa only [mem_inter_iff, mem_compl_iff, mem_singleton_iff] using hzgood.1
  · intro z hz
    have hzball : z ∈ ball s r :=
      closedBall_subset_ball (half_lt_self hr_pos) hz
    have hzgood := hr_ball hzball
    simpa only [mem_compl_iff, mem_riemannZetaZeros] using hzgood.2

/-- The circle about the shifted double pole `z = s` contributes the
order-one Laurent coefficient of the BCF kernel. -/
theorem circleIntegral_bcfShiftedZeroKernel_at_s
    {N : ℕ} {s : ℂ} {R : ℝ} (hN : N ≠ 0) (hR : 0 < R)
    (hone : ∀ z ∈ closedBall s R, z ≠ 1)
    (hzero : ∀ z ∈ closedBall s R, riemannZeta z ≠ 0) :
    (∮ z in C(s, R), bcfShiftedZeroKernel N s z) =
      2 * Real.pi * I *
        ((Real.log N : ℂ) / riemannZeta s -
          deriv riemannZeta s / (riemannZeta s) ^ 2) := by
  have hdiff : DifferentiableOn ℂ (bcfShiftedMainNumerator N s)
      (closedBall s R) :=
    differentiableOn_bcfShiftedMainNumerator hN hone hzero
  calc
    (∮ z in C(s, R), bcfShiftedZeroKernel N s z) =
        ∮ z in C(s, R), (1 / (z - s) ^ 2) • bcfShiftedMainNumerator N s z := by
      apply circleIntegral.integral_congr hR.le
      intro z _
      rw [bcfShiftedZeroKernel_eq_mainNumerator_div_sq]
      simp only [div_eq_mul_inv, smul_eq_mul]
      ring
    _ = (2 * Real.pi * I) • deriv (bcfShiftedMainNumerator N s) s :=
      hdiff.deriv_eq_smul_circleIntegral hR
    _ = 2 * Real.pi * I *
        ((Real.log N : ℂ) / riemannZeta s -
          deriv riemannZeta s / (riemannZeta s) ^ 2) := by
      rw [(hasDerivAt_bcfShiftedMainNumerator hN
        (hone s (mem_closedBall_self hR.le))
        (hzero s (mem_closedBall_self hR.le))).deriv]
      simp only [smul_eq_mul]

/-- A genuine outer-boundary deformation on a pole-free annulus: when the
annulus about `s` contains neither the zeta pole nor a zeta zero, the shifted
kernel has identical integrals on its inner and outer circles.  This is the
circle analogue of the deleted-rectangle step and uses Mathlib's annular
Cauchy--Goursat theorem. -/
theorem circleIntegral_bcfShiftedZeroKernel_eq_of_annulus
    {N : ℕ} {s : ℂ} {r R : ℝ} (hN : N ≠ 0)
    (hr : 0 < r) (hrR : r ≤ R)
    (hone : ∀ z ∈ closedBall s R \ ball s r, z ≠ 1)
    (hzero : ∀ z ∈ closedBall s R \ ball s r, riemannZeta z ≠ 0) :
    (∮ z in C(s, R), bcfShiftedZeroKernel N s z) =
      ∮ z in C(s, r), bcfShiftedZeroKernel N s z := by
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR countable_empty
  · intro z hz
    apply (bcfShiftedZeroKernel_differentiableAt hN (hone z hz) (hzero z hz) ?_).continuousAt
      |>.continuousWithinAt
    intro hzs
    subst z
    exact hz.2 (mem_ball_self hr)
  · intro z hz
    simp only [diff_empty] at hz
    have hzann : z ∈ closedBall s R \ ball s r := by
      refine ⟨ball_subset_closedBall hz.1, ?_⟩
      intro hzball
      exact hz.2 (ball_subset_closedBall hzball)
    apply bcfShiftedZeroKernel_differentiableAt hN
      (hone z hzann) (hzero z hzann)
    intro hzs
    subst z
    exact hz.2 (mem_closedBall_self hr.le)

/-- After the Perron normalization, the double-pole circle is exactly the
main term in BCF Lemma 2.  The nonzero logarithm hypothesis excludes `N = 1`,
where this normalization is not defined mathematically. -/
theorem normalized_circleIntegral_bcfShiftedZeroKernel_at_s_eq_mainTerm
    {N : ℕ} {s : ℂ} {R : ℝ} (hN : N ≠ 0)
    (hlog : (Real.log N : ℂ) ≠ 0) (hR : 0 < R)
    (hone : ∀ z ∈ closedBall s R, z ≠ 1)
    (hzero : ∀ z ∈ closedBall s R, riemannZeta z ≠ 0) :
    (Real.log N : ℂ)⁻¹ * (2 * Real.pi * I)⁻¹ *
      (∮ z in C(s, R), bcfShiftedZeroKernel N s z) =
        bcfLemma2MainTerm N s := by
  rw [circleIntegral_bcfShiftedZeroKernel_at_s hN hR hone hzero]
  unfold bcfLemma2MainTerm
  have hs_zero : riemannZeta s ≠ 0 :=
    hzero s (mem_closedBall_self hR.le)
  field_simp [hlog, hs_zero]

/-- The positively oriented local boundary of a deleted BCF contour: the
circle around the double pole `s`, followed by the circles around the finite
set of nontrivial-zero poles.  A deleted rectangle has this as its *inner*
boundary with the opposite orientation. -/
def bcfLocalDeletedBoundaryIntegral
    (N : ℕ) (s : ℂ) (R mainRadius : ℝ)
    (disks : BCFDeletedDiskFamily N s R) : ℂ :=
  (∮ z in C(s, mainRadius), bcfShiftedZeroKernel N s z) +
    bcfDeletedDiskBoundaryIntegral N s R disks

/-- The local boundary is exactly the main BCF term plus the finite
nontrivial-zero residue contribution after Perron normalization. -/
theorem normalized_bcfLocalDeletedBoundaryIntegral_eq_main_add_nontrivial
    {N : ℕ} {s : ℂ} {R mainRadius : ℝ}
    (disks : BCFDeletedDiskFamily N s R) (hN : N ≠ 0)
    (hlog : (Real.log N : ℂ) ≠ 0) (hmainRadius : 0 < mainRadius)
    (hone : ∀ z ∈ closedBall s mainRadius, z ≠ 1)
    (hzero : ∀ z ∈ closedBall s mainRadius, riemannZeta z ≠ 0) :
    (Real.log N : ℂ)⁻¹ * (2 * Real.pi * I)⁻¹ *
      bcfLocalDeletedBoundaryIntegral N s R mainRadius disks =
        bcfLemma2MainTerm N s +
          (Real.log N : ℂ)⁻¹ *
            bcfTruncatedSimpleZeroResidueSum N s R := by
  unfold bcfLocalDeletedBoundaryIntegral
  rw [show
    (∮ z in C(s, mainRadius), bcfShiftedZeroKernel N s z) =
      (2 * Real.pi * I) *
        ((Real.log N : ℂ) / riemannZeta s -
          deriv riemannZeta s / (riemannZeta s) ^ 2) by
      exact circleIntegral_bcfShiftedZeroKernel_at_s hN hmainRadius hone hzero,
    bcfDeletedDiskBoundaryIntegral_eq_two_pi_I_mul_residueSum disks hN]
  unfold bcfLemma2MainTerm
  have hs_zero : riemannZeta s ≠ 0 :=
    hzero s (mem_closedBall_self hmainRadius.le)
  field_simp [hlog, hs_zero, two_pi_I_ne_zero]

/-- The outer rectangular boundary after the coordinate change `z = s + w`.
It deliberately uses the established Perron-rectangle convention, so a
future geometric theorem must prove equality with this concrete expression. -/
def bcfShiftedRectangleBoundaryIntegral
    (N : ℕ) (s z w : ℂ) : ℂ :=
  bcfRectangleBoundaryIntegral N s (z - s) (w - s)

/-- The precise finite-pole contour-deformation target for the main pole and
the disk-truncated nontrivial zeros.  Its equality has the correct sign:
the boundary of a deleted rectangle is its counterclockwise outer boundary
minus the counterclockwise inner circles.

This proposition intentionally does not conceal a proof of the geometric
deleted-rectangle theorem.  Trivial-zero circles are a separate summand in
the eventual full deformation. -/
def BCFOuterBoundaryDeformation
    (N : ℕ) (s : ℂ) (R mainRadius : ℝ)
    (disks : BCFDeletedDiskFamily N s R) (z w : ℂ) : Prop :=
  bcfShiftedRectangleBoundaryIntegral N s z w =
    bcfLocalDeletedBoundaryIntegral N s R mainRadius disks

/-- Any proved deleted-rectangle deformation immediately has the expected
normalized main and nontrivial-zero terms.  This is the exact interface that
the remaining rectangle geometry feeds into the global Lemma 2 assembly. -/
theorem BCFOuterBoundaryDeformation.normalized_eq_main_add_nontrivial
    {N : ℕ} {s : ℂ} {R mainRadius : ℝ}
    (disks : BCFDeletedDiskFamily N s R) {z w : ℂ} (hN : N ≠ 0)
    (hlog : (Real.log N : ℂ) ≠ 0) (hmainRadius : 0 < mainRadius)
    (hone : ∀ u ∈ closedBall s mainRadius, u ≠ 1)
    (hzero : ∀ u ∈ closedBall s mainRadius, riemannZeta u ≠ 0)
    (hdeform : BCFOuterBoundaryDeformation N s R mainRadius disks z w) :
    (Real.log N : ℂ)⁻¹ * (2 * Real.pi * I)⁻¹ *
      bcfShiftedRectangleBoundaryIntegral N s z w =
        bcfLemma2MainTerm N s +
          (Real.log N : ℂ)⁻¹ *
            bcfTruncatedSimpleZeroResidueSum N s R := by
  rw [hdeform]
  exact normalized_bcfLocalDeletedBoundaryIntegral_eq_main_add_nontrivial
    disks hN hlog hmainRadius hone hzero

end

end NBMellinTools.H15BCF
