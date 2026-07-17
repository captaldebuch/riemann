/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.Hypotheses

/-!
# Conditional BCF formalization: deleted zero disks

This file supplies the finite local layer of the deleted-disk contour method.
Each isolated simple nontrivial zeta zero has a positive closed disk avoiding
every other zeta zero, the point `1`, and the kernel pole at `s`.  For any
finite disjoint family of such disks, the sum of their boundary integrals is
exactly `2πi` times the finite BCF simple-zero residue sum.

The remaining global step is geometric: identify the outer rectangular
boundary minus these circles with the remaining contour pieces, then prove
their limits.  No global deformation equality is asserted here.

Primary source: S. Bettin, J. B. Conrey, and D. W. Farmer,
*An optimal choice of Dirichlet polynomials for the Nyman--Beurling
criterion*, arXiv:1211.5191, Lemma 2.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Topology
open Complex Filter Metric Set

/-- Every zeta zero distinct from `1` and from the kernel pole `s` has a
positive closed disk on which it is the only zeta zero and which avoids both
exceptional points.  This uses Mathlib's discreteness theorem for the zeta
zero set. -/
theorem exists_bcfShiftedZeroKernel_isolatingRadius
    {s rho : ℂ} (hrho_zero : riemannZeta rho = 0)
    (hrho_one : rho ≠ 1) (hrho_s : rho ≠ s) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ closedBall rho r, z ≠ rho → z ≠ 1) ∧
      (∀ z ∈ closedBall rho r, z ≠ rho → riemannZeta z ≠ 0) ∧
      (∀ z ∈ closedBall rho r, z ≠ rho → z ≠ s) := by
  have hrho_mem : rho ∈ riemannZetaZeros := hrho_zero
  obtain ⟨r₀, hr₀_pos, hr₀_isolates⟩ :=
    Metric.exists_closedBall_inter_eq_singleton_of_discrete
      isDiscrete_riemannZetaZeros hrho_mem
  have hdist_one : 0 < dist rho 1 := dist_pos.mpr hrho_one
  have hdist_s : 0 < dist rho s := dist_pos.mpr hrho_s
  let r : ℝ := min r₀ (min (dist rho 1 / 2) (dist rho s / 2))
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min hr₀_pos (lt_min (half_pos hdist_one) (half_pos hdist_s))
  refine ⟨r, hr_pos, ?_, ?_, ?_⟩
  · intro z hz hzr hzone
    have hzle : dist z rho ≤ r := by simpa [Metric.mem_closedBall] using hz
    have hrle : r ≤ dist rho 1 / 2 := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hrlt : r < dist rho 1 :=
      lt_of_le_of_lt hrle (half_lt_self hdist_one)
    subst z
    apply (not_le_of_gt hrlt)
    simpa [dist_comm] using hzle
  · intro z hz hzr hzero
    have hzle : dist z rho ≤ r := by simpa [Metric.mem_closedBall] using hz
    have hrle : r ≤ r₀ := by
      dsimp [r]
      exact min_le_left _ _
    have hz_closed : z ∈ closedBall rho r₀ := by
      rw [Metric.mem_closedBall]
      exact hzle.trans hrle
    have hz_mem : z ∈ closedBall rho r₀ ∩ riemannZetaZeros :=
      ⟨hz_closed, hzero⟩
    rw [hr₀_isolates] at hz_mem
    exact hzr (by simpa using hz_mem)
  · intro z hz hzr hzs
    have hzle : dist z rho ≤ r := by simpa [Metric.mem_closedBall] using hz
    have hrle : r ≤ dist rho s / 2 := by
      dsimp [r]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hrlt : r < dist rho s :=
      lt_of_le_of_lt hrle (half_lt_self hdist_s)
    subst z
    apply (not_le_of_gt hrlt)
    simpa [dist_comm] using hzle

/-- A finite, pairwise disjoint collection of isolated circles around the
disk-truncated nontrivial zeta zeros.  The `pairwise_disjoint` field is the
geometric input needed by the later outer-boundary deformation; the residue
assembly below uses the already-proved local circle formulas. -/
structure BCFDeletedDiskFamily (N : ℕ) (s : ℂ) (R : ℝ) where
  radius : ℂ → ℝ
  radius_pos : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R → 0 < radius rho
  simple : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R → deriv riemannZeta rho ≠ 0
  center_ne_s : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R → rho ≠ s
  avoids_one : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R →
    ∀ z ∈ closedBall rho (radius rho), z ≠ rho → z ≠ 1
  avoids_other_zeros : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R →
    ∀ z ∈ closedBall rho (radius rho), z ≠ rho → riemannZeta z ≠ 0
  avoids_s : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R →
    ∀ z ∈ closedBall rho (radius rho), z ≠ rho → z ≠ s
  pairwise_disjoint : ∀ ⦃rho rho' : ℂ⦄,
    rho ∈ bcfTruncatedZeros R → rho' ∈ bcfTruncatedZeros R → rho ≠ rho' →
      Disjoint (closedBall rho (radius rho)) (closedBall rho' (radius rho'))

/-- The finite sum of the small-circle boundary integrals associated to a
deleted-disk family. -/
def bcfDeletedDiskBoundaryIntegral
    (N : ℕ) (s : ℂ) (R : ℝ) (disks : BCFDeletedDiskFamily N s R) : ℂ :=
  ∑ rho ∈ bcfTruncatedZeros R,
    ∮ z in C(rho, disks.radius rho), bcfShiftedZeroKernel N s z

private theorem truncated_zero_ne_one {R : ℝ} {rho : ℂ}
    (hrho : rho ∈ bcfTruncatedZeros R) : rho ≠ 1 := by
  intro hrho_one
  have hlt : rho.re < 1 := (mem_bcfTruncatedZeros.mp hrho).2.2.2
  rw [hrho_one] at hlt
  norm_num at hlt

/-- A finite disk truncation of nontrivial simple zeros admits a family of
positive, pairwise-disjoint closed isolation disks.  Starting with the local
closed disks from `exists_bcfShiftedZeroKernel_isolatingRadius`, we halve all
radii; this preserves the local exclusions and makes distinct disks disjoint. -/
theorem exists_bcfDeletedDiskFamily
    {N : ℕ} {s : ℂ} {R : ℝ}
    (hsimple : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R → deriv riemannZeta rho ≠ 0)
    (hcenter_ne_s : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R → rho ≠ s) :
    Nonempty (BCFDeletedDiskFamily N s R) := by
  classical
  have hlocal : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R →
      ∃ r : ℝ, 0 < r ∧
        (∀ z ∈ closedBall rho r, z ≠ rho → z ≠ 1) ∧
        (∀ z ∈ closedBall rho r, z ≠ rho → riemannZeta z ≠ 0) ∧
        (∀ z ∈ closedBall rho r, z ≠ rho → z ≠ s) := by
    intro rho hrho
    exact exists_bcfShiftedZeroKernel_isolatingRadius
      (mem_bcfTruncatedZeros.mp hrho).2.1
      (truncated_zero_ne_one hrho) (hcenter_ne_s rho hrho)
  let radius : ℂ → ℝ := fun rho =>
    if h : rho ∈ bcfTruncatedZeros R then Classical.choose (hlocal rho h) else 1
  have hradius : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R →
      0 < radius rho ∧
        (∀ z ∈ closedBall rho (radius rho), z ≠ rho → z ≠ 1) ∧
        (∀ z ∈ closedBall rho (radius rho), z ≠ rho → riemannZeta z ≠ 0) ∧
        (∀ z ∈ closedBall rho (radius rho), z ≠ rho → z ≠ s) := by
    intro rho hrho
    simp only [radius, dif_pos hrho]
    exact Classical.choose_spec (hlocal rho hrho)
  refine ⟨
    { radius := fun rho => radius rho / 2
      radius_pos := fun rho hrho => half_pos (hradius rho hrho).1
      simple := hsimple
      center_ne_s := hcenter_ne_s
      avoids_one := fun rho hrho z hz hzr =>
        (hradius rho hrho).2.1 z
          (Metric.closedBall_subset_closedBall
            (by linarith [(hradius rho hrho).1]) hz) hzr
      avoids_other_zeros := fun rho hrho z hz hzr =>
        (hradius rho hrho).2.2.1 z
          (Metric.closedBall_subset_closedBall
            (by linarith [(hradius rho hrho).1]) hz) hzr
      avoids_s := fun rho hrho z hz hzr =>
        (hradius rho hrho).2.2.2 z
          (Metric.closedBall_subset_closedBall
            (by linarith [(hradius rho hrho).1]) hz) hzr
      pairwise_disjoint := by
        intro rho rho' hrho hrho' hne
        apply Metric.closedBall_disjoint_closedBall
        have hrho_lt : radius rho < dist rho rho' := by
          apply lt_of_not_ge
          intro hdist
          have hmem : rho' ∈ closedBall rho (radius rho) :=
            Metric.mem_closedBall'.mpr hdist
          exact (hradius rho hrho).2.2.1 rho' hmem hne.symm
            (mem_bcfTruncatedZeros.mp hrho').2.1
        have hrho'_lt : radius rho' < dist rho rho' := by
          apply lt_of_not_ge
          intro hdist
          have hmem : rho ∈ closedBall rho' (radius rho') := by
            rw [Metric.mem_closedBall']
            simpa [dist_comm] using hdist
          exact (hradius rho' hrho').2.2.1 rho hmem hne
            (mem_bcfTruncatedZeros.mp hrho).2.1
        linarith }⟩

/-- The Phase 5 simplicity package supplies the local simplicity input for
the concrete finite deleted-disk construction. -/
theorem exists_bcfDeletedDiskFamily_of_hypotheses
    {N : ℕ} {s : ℂ} {R : ℝ} (h : BCFConditionalHypotheses)
    (hcenter_ne_s : ∀ rho : ℂ, rho ∈ bcfTruncatedZeros R → rho ≠ s) :
    Nonempty (BCFDeletedDiskFamily N s R) := by
  apply exists_bcfDeletedDiskFamily
  · intro rho hrho
    apply h.simplicity.simple_nontrivial rho
    rw [mem_bcfNontrivialZetaZeros]
    exact ⟨(mem_bcfTruncatedZeros.mp hrho).2.1,
      (mem_bcfTruncatedZeros.mp hrho).2.2.1,
      (mem_bcfTruncatedZeros.mp hrho).2.2.2⟩
  · exact hcenter_ne_s

/-- Every circle in a deleted-disk family has the explicit BCF simple-zero
residue integral. -/
theorem BCFDeletedDiskFamily.circleIntegral_eq_residue
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R)
    (hN : N ≠ 0) {rho : ℂ} (hrho : rho ∈ bcfTruncatedZeros R) :
    (∮ z in C(rho, disks.radius rho), bcfShiftedZeroKernel N s z) =
      2 * Real.pi * I * bcfSimpleZeroResidue N s rho := by
  apply bcfShiftedZeroKernel_circleIntegral
  · exact disks.radius_pos rho hrho
  · exact hN
  · exact truncated_zero_ne_one hrho
  · exact (mem_bcfTruncatedZeros.mp hrho).2.1
  · exact disks.simple rho hrho
  · exact disks.center_ne_s rho hrho
  · exact disks.avoids_one rho hrho
  · exact disks.avoids_other_zeros rho hrho
  · exact disks.avoids_s rho hrho

/-- The deleted-disk boundary contribution is exactly `2πi` times the finite
distinct nontrivial-zero residue sum. -/
theorem bcfDeletedDiskBoundaryIntegral_eq_two_pi_I_mul_residueSum
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R)
    (hN : N ≠ 0) :
    bcfDeletedDiskBoundaryIntegral N s R disks =
      2 * Real.pi * I * bcfTruncatedSimpleZeroResidueSum N s R := by
  unfold bcfDeletedDiskBoundaryIntegral bcfTruncatedSimpleZeroResidueSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact disks.circleIntegral_eq_residue hN hrho

end

end NBMellinTools.H15BCF
