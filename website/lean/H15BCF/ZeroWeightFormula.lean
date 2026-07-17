/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import Mathlib.Topology.Order.MonotoneConvergence
import NBMellinTools.H15BCF.Hypotheses

/-!
# Finite calculus for the BCF zero-weight formula

This file formalizes the unconditional algebra that surrounds the remaining
classical zero-weight formula in the Bettin--Conrey--Farmer argument.

In particular, it proves that the truncated distinct-zero weights form a
monotone family, transports nontrivial zeros through the completed-zeta
functional equation, and reduces the analytic zero-weight formula to two
precise statements: boundedness of the truncations and identification of their
conditional supremum.

It deliberately does **not** assert either analytic statement.  Mathlib has
the completed zeta function and its functional equation, but does not yet
contain the Hadamard-product / logarithmic-derivative analysis needed to prove
the required supremum identity.  Keeping that boundary explicit prevents the
formal development from treating the BCF leading constant as established.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Theorem 1.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Set

/-- Enlarging the height cutoff can only add nontrivial zeta zeros. -/
theorem bcfZerosUpToHeight_mono {T U : ℝ} (hTU : T ≤ U) :
    bcfZerosUpToHeight T ⊆ bcfZerosUpToHeight U := by
  intro rho hrho
  rw [mem_bcfZerosUpToHeight] at hrho ⊢
  exact ⟨hrho.1, hrho.2.1, hrho.2.2.1, hrho.2.2.2.trans hTU⟩

/-- Every individual reciprocal squared-norm weight is nonnegative. -/
theorem bcfZeroWeightTerm_nonneg (rho : ℂ) :
    0 ≤ 1 / ‖rho‖ ^ 2 := by
  positivity

/-- A zero in the nontrivial strip is nonzero, so its reciprocal squared-norm
weight is strictly positive. -/
theorem bcfZeroWeightTerm_pos {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    0 < 1 / ‖rho‖ ^ 2 := by
  rw [mem_bcfZerosUpToHeight] at hrho
  have hrho_ne_zero : rho ≠ 0 := by
    intro hzero
    have hre := hrho.2.1
    rw [hzero] at hre
    norm_num at hre
  exact div_pos zero_lt_one (pow_pos (norm_pos_iff.mpr hrho_ne_zero) 2)

/-- The finite distinct-zero weight sums are monotone in their height cutoff. -/
theorem bcfZeroWeightSumUpToHeight_monotone :
    Monotone bcfZeroWeightSumUpToHeight := by
  intro T U hTU
  unfold bcfZeroWeightSumUpToHeight
  exact Finset.sum_le_sum_of_subset_of_nonneg (bcfZerosUpToHeight_mono hTU)
    fun rho _ _ ↦ bcfZeroWeightTerm_nonneg rho

/-- The analytic boundedness assertion required to turn monotone finite
zero-weight sums into a real limit. -/
def BCFZeroWeightBounded : Prop :=
  BddAbove (Set.range bcfZeroWeightSumUpToHeight)

/-- The scalar output of the missing completed-zeta product argument: the
conditional supremum of the increasing distinct-zero sums has the BCF
constant as its value. -/
def BCFZeroWeightSupremumIdentity : Prop :=
  (⨆ T : ℝ, bcfZeroWeightSumUpToHeight T) = bcfAsymptoticConstant

/-- A bounded monotone family converges to its conditional supremum.  Thus a
future completed-zeta/Hadamard proof has a small, exact interface to the
already-stated `BCFZeroWeightFormula`. -/
theorem bcfZeroWeightFormula_of_bounded_supremum
    (hbounded : BCFZeroWeightBounded)
    (hsup : BCFZeroWeightSupremumIdentity) :
    BCFZeroWeightFormula := by
  unfold BCFZeroWeightFormula BCFZeroWeightBounded BCFZeroWeightSupremumIdentity at *
  simpa only [hsup] using
    (tendsto_atTop_ciSup bcfZeroWeightSumUpToHeight_monotone hbounded)

/-- A nontrivial zeta zero is also a zero of Mathlib's completed zeta
function.  The positive real part is exactly what makes the gamma factor
nonzero. -/
theorem completedRiemannZeta_zero_of_mem_bcfZerosUpToHeight
    {T : ℝ} {rho : ℂ} (hrho : rho ∈ bcfZerosUpToHeight T) :
    completedRiemannZeta rho = 0 := by
  rw [mem_bcfZerosUpToHeight] at hrho
  have hrho_ne_zero : rho ≠ 0 := by
    intro hzero
    have hre := hrho.2.1
    rw [hzero] at hre
    norm_num at hre
  have hzeta : completedRiemannZeta rho / Gammaℝ rho = 0 := by
    rw [← riemannZeta_def_of_ne_zero hrho_ne_zero]
    exact hrho.1
  rcases (div_eq_zero_iff.mp hzeta) with hcompleted | hgamma
  · exact hcompleted
  · exact (Gammaℝ_ne_zero_of_re_pos hrho.2.1 hgamma).elim

/-- The completed-zeta functional equation transports a nontrivial zero at
`rho` to the reflected nontrivial zero at `1 - rho`, without changing the
height cutoff. -/
theorem one_sub_mem_bcfZerosUpToHeight {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    1 - rho ∈ bcfZerosUpToHeight T := by
  rw [mem_bcfZerosUpToHeight] at hrho ⊢
  have hrho_ne_one : rho ≠ 1 := by
    intro h
    have hre := hrho.2.2.1
    rw [h] at hre
    norm_num at hre
  have hsub_ne_zero : 1 - rho ≠ 0 :=
    sub_ne_zero.mpr fun h ↦ hrho_ne_one h.symm
  have hcompleted : completedRiemannZeta rho = 0 :=
    completedRiemannZeta_zero_of_mem_bcfZerosUpToHeight (by
      rw [mem_bcfZerosUpToHeight]
      exact hrho)
  have hzeta : riemannZeta (1 - rho) = 0 := by
    rw [riemannZeta_def_of_ne_zero hsub_ne_zero,
      completedRiemannZeta_one_sub, hcompleted]
    simp
  refine ⟨hzeta, ?_, ?_, ?_⟩
  · simpa using sub_pos.mpr hrho.2.2.1
  · simp only [sub_re, one_re]
    linarith [hrho.2.1]
  · simpa using hrho.2.2.2

/-- Reflection about the critical line is an involution of every finite BCF
zero truncation. -/
theorem one_sub_mem_bcfZerosUpToHeight_iff {T : ℝ} {rho : ℂ} :
    1 - rho ∈ bcfZerosUpToHeight T ↔ rho ∈ bcfZerosUpToHeight T := by
  constructor
  · intro h
    have h' := one_sub_mem_bcfZerosUpToHeight (rho := 1 - rho) h
    convert h' using 1
    ring
  · exact one_sub_mem_bcfZerosUpToHeight

/-- Under RH, reflection has the same norm as the original zero.  This is the
finite symmetry needed when a product-formula argument pairs critical-line
zeros. -/
theorem norm_one_sub_eq_norm_of_re_eq_half {rho : ℂ}
    (hre : rho.re = 1 / 2) :
    ‖1 - rho‖ = ‖rho‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, zero_sub]
  rw [hre]
  ring

/-- Under the BCF RH hypothesis, reflection preserves every finite
reciprocal-norm zero weight. -/
theorem bcfZeroWeightTerm_one_sub_eq_of_rh
    (hRH : RiemannHypothesisHypothesis) {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfZerosUpToHeight T) :
    1 / ‖1 - rho‖ ^ 2 = 1 / ‖rho‖ ^ 2 := by
  rw [norm_one_sub_eq_norm_of_re_eq_half (hRH.re_eq_half hrho)]

end

end NBMellinTools.H15BCF
