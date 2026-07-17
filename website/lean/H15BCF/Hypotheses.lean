/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import NBMellinTools.H15BCF.ContourShift
import NBMellinTools.NB5FunctionalEquationClosure

/-!
# Conditional BCF formalization: zeta-zero hypotheses

This file states the three assumptions used after BCF Lemma 2:

* the Riemann hypothesis on the open critical strip;
* simplicity of the nontrivial zeta zeros;
* the reciprocal zeta-derivative moment bound from equation (2) of
  Bettin--Conrey--Farmer.

The cutoff in the moment condition is exactly `|im rho| ≤ T`, as in the
paper.  The finite zero set is constructed from Mathlib's discreteness theorem
for the zeta zeros, so every displayed sum is an actual `Finset` sum.

Lean defines inversion at zero by `0⁻¹ = 0`.  Therefore a formal moment bound
cannot implicitly express zero simplicity: simplicity is retained as a
separate explicit hypothesis and bundled with RH and the moment bound in
`BCFConditionalHypotheses`.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Theorem 1 and equation (2).
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Asymptotics Complex Filter Metric Set

/-- The nontrivial zeta zeros whose imaginary part has absolute value at most
`T`.  This is a set before its finiteness is packaged as a `Finset`. -/
def bcfZerosUpToHeightSet (T : ℝ) : Set ℂ :=
  {rho | rho ∈ bcfNontrivialZetaZeros ∧ |rho.im| ≤ T}

/-- A nontrivial zero with `|im rho| ≤ T` lies in the disk of radius
`|T| + 1`. -/
theorem bcfZerosUpToHeightSet_subset_disk (T : ℝ) :
    bcfZerosUpToHeightSet T ⊆ bcfZerosInDisk (|T| + 1) := by
  intro rho hrho
  have hT : 0 ≤ T := (abs_nonneg rho.im).trans hrho.2
  constructor
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact (calc
      ‖rho‖ ≤ |rho.re| + |rho.im| := norm_le_abs_re_add_abs_im rho
      _ = rho.re + |rho.im| := by rw [abs_of_pos hrho.1.2.1]
      _ < 1 + T := add_lt_add_of_lt_of_le hrho.1.2.2 hrho.2
      _ = |T| + 1 := by rw [abs_of_nonneg hT]; ring).le
  · exact hrho.1

/-- There are finitely many nontrivial zeta zeros up to any fixed imaginary
height. -/
theorem bcfZerosUpToHeightSet_finite (T : ℝ) :
    (bcfZerosUpToHeightSet T).Finite :=
  (bcfZerosInDisk_finite (|T| + 1)).subset
    (bcfZerosUpToHeightSet_subset_disk T)

/-- The finite set of distinct nontrivial zeta zeros with `|im rho| ≤ T`. -/
def bcfZerosUpToHeight (T : ℝ) : Finset ℂ :=
  (bcfZerosUpToHeightSet_finite T).toFinset

@[simp]
theorem mem_bcfZerosUpToHeight {T : ℝ} {rho : ℂ} :
    rho ∈ bcfZerosUpToHeight T ↔
      riemannZeta rho = 0 ∧ 0 < rho.re ∧ rho.re < 1 ∧ |rho.im| ≤ T := by
  simp [bcfZerosUpToHeight, bcfZerosUpToHeightSet,
    mem_bcfNontrivialZetaZeros, and_assoc]

/-- The finite reciprocal-derivative moment from BCF equation (2). -/
def bcfReciprocalZetaDerivMoment (T : ℝ) : ℝ :=
  ∑ rho ∈ bcfZerosUpToHeight T, 1 / ‖deriv riemannZeta rho‖ ^ 2

/-- Every finite reciprocal-derivative moment is nonnegative. -/
theorem bcfReciprocalZetaDerivMoment_nonneg (T : ℝ) :
    0 ≤ bcfReciprocalZetaDerivMoment T := by
  unfold bcfReciprocalZetaDerivMoment
  positivity

/-- The finite distinct-zero weight sum used in the simple-zero form of the
BCF leading constant. -/
def bcfZeroWeightSumUpToHeight (T : ℝ) : ℝ :=
  ∑ rho ∈ bcfZerosUpToHeight T, 1 / ‖rho‖ ^ 2

/-- The constant in the BCF asymptotic. -/
def bcfAsymptoticConstant : ℝ :=
  2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- Critical-strip formulation of RH used by the BCF argument.  It reuses
the formulation already established by NB5 rather than introducing a second
incompatible definition. -/
structure RiemannHypothesisHypothesis : Prop where
  criticalStrip : NBMellinTools.NB5.CriticalStripRiemannHypothesis

/-- Simplicity of every nontrivial zeta zero.  Trivial zeros are deliberately
outside the scope of this hypothesis. -/
structure ZeroSimplicityHypothesis : Prop where
  simple_nontrivial :
    ∀ rho : ℂ, rho ∈ bcfNontrivialZetaZeros → deriv riemannZeta rho ≠ 0

/-- BCF equation (2): for some `delta > 0`, the reciprocal derivative moment
is `O(T^(3/2-delta))` as `T → ∞`. -/
structure ZetaDerivativeMomentHypothesis where
  delta : ℝ
  delta_pos : 0 < delta
  moment_isBigO :
    (bcfReciprocalZetaDerivMoment =O[atTop]
      fun T : ℝ ↦ T ^ ((3 / 2 : ℝ) - delta))

/-- The complete explicit assumption package for the conditional BCF
asymptotic. -/
structure BCFConditionalHypotheses where
  rh : RiemannHypothesisHypothesis
  simplicity : ZeroSimplicityHypothesis
  derivativeMoment : ZetaDerivativeMomentHypothesis

/-- Mathlib's global formulation of RH implies the critical-strip
formulation used here. -/
theorem RiemannHypothesisHypothesis.of_mathlib
    (h : RiemannHypothesis) : RiemannHypothesisHypothesis := by
  constructor
  intro s hs0 hs1 hzeta
  apply h s hzeta
  · intro htrivial
    rcases htrivial with ⟨n, hn⟩
    have hre : s.re = -2 * (n + 1 : ℝ) := by
      rw [hn]
      norm_num
    have hn : 0 ≤ (n + 1 : ℝ) := by positivity
    nlinarith
  · intro hs
    subst s
    norm_num at hs1

/-- RH places every member of a finite BCF zero truncation on the critical
line. -/
theorem RiemannHypothesisHypothesis.re_eq_half
    (h : RiemannHypothesisHypothesis) {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    rho.re = 1 / 2 := by
  rw [mem_bcfZerosUpToHeight] at hrho
  exact h.criticalStrip rho hrho.2.1 hrho.2.2.1 hrho.1

/-- The simplicity hypothesis supplies the nonvanishing derivative needed by
the Phase 4 residue formula. -/
theorem ZeroSimplicityHypothesis.deriv_ne_zero
    (h : ZeroSimplicityHypothesis) {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    deriv riemannZeta rho ≠ 0 := by
  apply h.simple_nontrivial rho
  rw [mem_bcfNontrivialZetaZeros]
  rw [mem_bcfZerosUpToHeight] at hrho
  exact ⟨hrho.1, hrho.2.1, hrho.2.2.1⟩

/-- Under simplicity, every summand in the derivative moment is strictly
positive. -/
theorem reciprocalZetaDerivMomentTerm_pos
    (h : ZeroSimplicityHypothesis) {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    0 < 1 / ‖deriv riemannZeta rho‖ ^ 2 := by
  have hderiv : deriv riemannZeta rho ≠ 0 := h.deriv_ne_zero hrho
  exact div_pos zero_lt_one (pow_pos (norm_pos_iff.mpr hderiv) 2)

/-- On the critical line, the squared norm is `1/4 + (im rho)^2`. -/
theorem norm_sq_eq_quarter_add_im_sq_of_re_eq_half
    {rho : ℂ} (hrho : rho.re = 1 / 2) :
    ‖rho‖ ^ 2 = 1 / 4 + rho.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, hrho]
  ring

/-- RH rewrites each finite zero-weight sum in critical-line coordinates. -/
theorem bcfZeroWeightSumUpToHeight_eq_criticalLine
    (h : RiemannHypothesisHypothesis) (T : ℝ) :
    bcfZeroWeightSumUpToHeight T =
      ∑ rho ∈ bcfZerosUpToHeight T, 1 / (1 / 4 + rho.im ^ 2) := by
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [norm_sq_eq_quarter_add_im_sq_of_re_eq_half (h.re_eq_half hrho)]

/-- The precise distinct-zero limit needed for the leading constant once
simplicity has reduced multiplicities to one.

This is a named open proposition, not a theorem or an additional hypothesis
hidden inside `BCFConditionalHypotheses`. -/
def BCFZeroWeightFormula : Prop :=
  Tendsto bcfZeroWeightSumUpToHeight atTop (𝓝 bcfAsymptoticConstant)

/-- Phase 5 supplies all explicit assumptions needed by the simple-zero local
residue theorem from Phase 4. -/
theorem bcfShiftedZeroKernel_hasSimplePoleResidueAt_of_hypotheses
    (h : BCFConditionalHypotheses)
    {N : ℕ} {s rho : ℂ} {T : ℝ}
    (hN : N ≠ 0) (hrho : rho ∈ bcfZerosUpToHeight T)
    (hrho_s : rho ≠ s) :
    HasSimplePoleResidueAt (bcfShiftedZeroKernel N s) rho
      (bcfSimpleZeroResidue N s rho) := by
  rw [mem_bcfZerosUpToHeight] at hrho
  apply bcfShiftedZeroKernel_hasSimplePoleResidueAt hN
  · intro hrho_one
    subst rho
    norm_num at hrho
  · exact hrho.1
  · exact h.simplicity.simple_nontrivial _
      (by rw [mem_bcfNontrivialZetaZeros]; exact ⟨hrho.1, hrho.2.1, hrho.2.2.1⟩)
  · exact hrho_s

end

end NBMellinTools.H15BCF
