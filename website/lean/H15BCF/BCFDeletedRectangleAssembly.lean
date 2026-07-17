/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.FiniteDeletedRectangleAssembly
import NBMellinTools.H15BCF.FiniteAxisSeparation

/-!
# BCF specialization of finite deleted-rectangle assembly

This file connects the generic deleted-rectangle theorem to the shifted BCF
kernel.  The first ingredient is translation compatibility between the
Perron-coordinate rectangle and the corresponding shifted rectangle.
-/

namespace NBMellinTools.H15BCF

noncomputable section

open scoped BigOperators Interval Topology
open Complex MeasureTheory Metric intervalIntegral

/-- Translating both the integrand and the rectangular contour gives the same
oriented rectangle boundary integral. -/
theorem rectangleBoundaryIntegral_translate_sub
    (f : ℂ → ℂ) (s z w : ℂ) :
    rectangleBoundaryIntegral (fun u ↦ f (u - s)) z w =
      rectangleBoundaryIntegral f (z - s) (w - s) := by
  unfold rectangleBoundaryIntegral
  have hbottom :
      (∫ x : ℝ in z.re..w.re, (fun u ↦ f (u - s)) (x + z.im * I)) =
        ∫ x : ℝ in z.re..w.re,
          f (((x - s.re : ℝ) : ℂ) + (z.im - s.im) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply congrArg f
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have htop :
      (∫ x : ℝ in z.re..w.re, (fun u ↦ f (u - s)) (x + w.im * I)) =
        ∫ x : ℝ in z.re..w.re,
          f (((x - s.re : ℝ) : ℂ) + (w.im - s.im) * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply congrArg f
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hright :
      (∫ y : ℝ in z.im..w.im, (fun u ↦ f (u - s)) (w.re + y * I)) =
        ∫ y : ℝ in z.im..w.im,
          f ((w.re - s.re) + ((y - s.im : ℝ) : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y _
    apply congrArg f
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hleft :
      (∫ y : ℝ in z.im..w.im, (fun u ↦ f (u - s)) (z.re + y * I)) =
        ∫ y : ℝ in z.im..w.im,
          f ((z.re - s.re) + ((y - s.im : ℝ) : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y _
    apply congrArg f
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hbottom, htop, hright, hleft,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦
      f (x + (z.im - s.im) * I)) s.re,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦
      f (x + (w.im - s.im) * I)) s.re,
    intervalIntegral.integral_comp_sub_right (fun y : ℝ ↦
      f ((w.re - s.re) + y * I)) s.im,
    intervalIntegral.integral_comp_sub_right (fun y : ℝ ↦
      f ((z.re - s.re) + y * I)) s.im]
  simp only [Complex.sub_re, Complex.sub_im]
  push_cast
  rfl

/-- The shifted BCF rectangle convention is the generic rectangle boundary
integral of the shifted zero kernel. -/
theorem bcfShiftedRectangleBoundaryIntegral_eq_rectangleBoundaryIntegral_shiftedZeroKernel
    (N : ℕ) (s z w : ℂ) :
    bcfShiftedRectangleBoundaryIntegral N s z w =
      rectangleBoundaryIntegral (bcfShiftedZeroKernel N s) z w := by
  calc
    bcfShiftedRectangleBoundaryIntegral N s z w =
        bcfRectangleBoundaryIntegral N s (z - s) (w - s) := rfl
    _ = rectangleBoundaryIntegral (bcfPerronKernel N s) (z - s) (w - s) :=
      bcfRectangleBoundaryIntegral_eq_rectangleBoundaryIntegral N s (z - s) (w - s)
    _ = rectangleBoundaryIntegral (fun u ↦ bcfPerronKernel N s (u - s)) z w :=
      (rectangleBoundaryIntegral_translate_sub (bcfPerronKernel N s) s z w).symm
    _ = rectangleBoundaryIntegral (bcfShiftedZeroKernel N s) z w := by
      congr 1
      funext u
      exact bcfPerronKernel_sub N s u

/-- Uniformly shrinking a finite deleted-zero family preserves every local
exclusion and pairwise disjointness property.  This lets a later geometric
construction introduce a positive separation margin without changing the
finite residue contribution. -/
def BCFDeletedDiskFamily.scale
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R)
    (q : ℝ) (hq : 0 < q) (hq_one : q ≤ 1) : BCFDeletedDiskFamily N s R where
  radius := fun rho => q * disks.radius rho
  radius_pos := fun rho hrho => mul_pos hq (disks.radius_pos rho hrho)
  simple := disks.simple
  center_ne_s := disks.center_ne_s
  avoids_one := by
    intro rho hrho u hu hu_ne
    exact disks.avoids_one rho hrho u
      (Metric.closedBall_subset_closedBall (by
        calc
          q * disks.radius rho ≤ 1 * disks.radius rho :=
            mul_le_mul_of_nonneg_right hq_one (disks.radius_pos rho hrho).le
          _ = disks.radius rho := one_mul _) hu) hu_ne
  avoids_other_zeros := by
    intro rho hrho u hu hu_ne
    exact disks.avoids_other_zeros rho hrho u
      (Metric.closedBall_subset_closedBall (by
        calc
          q * disks.radius rho ≤ 1 * disks.radius rho :=
            mul_le_mul_of_nonneg_right hq_one (disks.radius_pos rho hrho).le
          _ = disks.radius rho := one_mul _) hu) hu_ne
  avoids_s := by
    intro rho hrho u hu hu_ne
    exact disks.avoids_s rho hrho u
      (Metric.closedBall_subset_closedBall (by
        calc
          q * disks.radius rho ≤ 1 * disks.radius rho :=
            mul_le_mul_of_nonneg_right hq_one (disks.radius_pos rho hrho).le
          _ = disks.radius rho := one_mul _) hu) hu_ne
  pairwise_disjoint := by
    intro rho rho' hrho hrho' hne
    apply Disjoint.mono
      (Metric.closedBall_subset_closedBall (by
        calc
          q * disks.radius rho ≤ 1 * disks.radius rho :=
            mul_le_mul_of_nonneg_right hq_one (disks.radius_pos rho hrho).le
          _ = disks.radius rho := one_mul _))
      (Metric.closedBall_subset_closedBall (by
        calc
          q * disks.radius rho' ≤ 1 * disks.radius rho' :=
            mul_le_mul_of_nonneg_right hq_one (disks.radius_pos rho' hrho').le
          _ = disks.radius rho' := one_mul _))
    exact disks.pairwise_disjoint hrho hrho' hne

/-- Shrinking a BCF deleted-disk family leaves its finite circle contribution
unchanged: both families compute the same residue sum. -/
theorem bcfDeletedDiskBoundaryIntegral_scale_eq
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R)
    (q : ℝ) (hq : 0 < q) (hq_one : q ≤ 1) (hN : N ≠ 0) :
    bcfDeletedDiskBoundaryIntegral N s R (disks.scale q hq hq_one) =
      bcfDeletedDiskBoundaryIntegral N s R disks := by
  rw [bcfDeletedDiskBoundaryIntegral_eq_two_pi_I_mul_residueSum
        (disks.scale q hq hq_one) hN,
      bcfDeletedDiskBoundaryIntegral_eq_two_pi_I_mul_residueSum disks hN]

/-- A point outside finitely many closed disks has a positive closed disk
disjoint from every one of them.  This is the finite-separation lemma needed
to add the BCF main-pole disk to the already pairwise-disjoint zero disks. -/
theorem exists_pos_radius_disjoint_from_finset_closedBalls
    (c : ℂ) (holes : Finset ℂ) (radius : ℂ → ℝ)
    (havoid : ∀ rho ∈ holes, c ∉ closedBall rho (radius rho)) :
    ∃ r : ℝ, 0 < r ∧
      ∀ rho ∈ holes, Disjoint (closedBall c r) (closedBall rho (radius rho)) := by
  classical
  induction holes using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro rho hrho
      simp at hrho
  | @insert a holes ha ih =>
      have havoid_tail : ∀ rho ∈ holes, c ∉ closedBall rho (radius rho) :=
        fun rho hrho ↦ havoid rho (by simp [hrho])
      obtain ⟨r, hr, hdisj⟩ := ih havoid_tail
      have hnot : c ∉ closedBall a (radius a) := havoid a (by simp)
      have hlt : radius a < dist c a :=
        lt_of_not_ge fun hle ↦ hnot (Metric.mem_closedBall.mpr hle)
      let δ : ℝ := (dist c a - radius a) / 2
      have hδ : 0 < δ := half_pos (sub_pos.mpr hlt)
      refine ⟨min r δ, lt_min hr hδ, ?_⟩
      intro rho hrho
      rw [Finset.mem_insert] at hrho
      rcases hrho with rfl | hrho
      · apply Metric.closedBall_disjoint_closedBall
        have hle : min r δ ≤ δ := min_le_right _ _
        dsimp [δ] at hle
        linarith
      · apply Disjoint.mono
          (Metric.closedBall_subset_closedBall (min_le_left _ _)) (by rfl)
        exact hdisj rho hrho

/-- The regular BCF main pole admits a closed disk that avoids the zeta pole,
all zeta zeros, and every disk in a finite deleted-zero family. -/
theorem exists_bcfShiftedMainPoleRadius_disjoint_from_deletedDisks
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R)
    (hs_one : s ≠ 1) (hs_zero : riemannZeta s ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ closedBall s r, u ≠ 1) ∧
      (∀ u ∈ closedBall s r, riemannZeta u ≠ 0) ∧
      (∀ rho ∈ bcfTruncatedZeros R,
        Disjoint (closedBall s r) (closedBall rho (disks.radius rho))) := by
  obtain ⟨r₀, hr₀, hone, hzero⟩ := exists_bcfShiftedMainPoleRadius hs_one hs_zero
  obtain ⟨r₁, hr₁, hdisj⟩ :=
    exists_pos_radius_disjoint_from_finset_closedBalls s (bcfTruncatedZeros R) disks.radius
      (fun rho hrho hmem ↦
        (disks.avoids_s rho hrho s hmem (disks.center_ne_s rho hrho).symm) rfl)
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_, ?_, ?_⟩
  · intro u hu
    exact hone u (Metric.closedBall_subset_closedBall (min_le_left _ _) hu)
  · intro u hu
    exact hzero u (Metric.closedBall_subset_closedBall (min_le_left _ _) hu)
  · intro rho hrho
    apply Disjoint.mono (Metric.closedBall_subset_closedBall (min_le_right _ _)) (by rfl)
    exact hdisj rho hrho

/-- The main-pole disk and all truncated nontrivial-zero disks, collected in
one finite indexing set. -/
def bcfAllDeletedHoles (R : ℝ) : Finset (Option ℂ) :=
  insert none ((bcfTruncatedZeros R).image some)

/-- Center of a disk in the BCF finite deleted-disk family. -/
def bcfDeletedHoleCenter (s : ℂ) : Option ℂ → ℂ
  | none => s
  | some rho => rho

/-- Radius of a disk in the BCF finite deleted-disk family. -/
def bcfDeletedHoleRadius
    {N : ℕ} {s : ℂ} {R : ℝ}
    (mainRadius : ℝ) (disks : BCFDeletedDiskFamily N s R) : Option ℂ → ℝ
  | none => mainRadius
  | some rho => disks.radius rho

/-- The finite collection of all BCF deleted-disk centers. -/
def bcfAllDeletedCenters (s : ℂ) (R : ℝ) : Finset ℂ :=
  (bcfAllDeletedHoles R).image (bcfDeletedHoleCenter s)

/-- The finite axis cuts selected from the main-pole and truncated-zero
centers. -/
noncomputable def bcfAllDeletedAxisCuts (s : ℂ) (R : ℝ) : Finset AxisCut :=
  allAxisCuts (bcfAllDeletedCenters s R)

/-- The BCF main center and the distinct truncated-zero centers are pairwise
different. -/
theorem bcfDeletedHoleCenter_injectiveOn
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R) :
    Set.InjOn (bcfDeletedHoleCenter s) (bcfAllDeletedHoles R) := by
  intro hole hhole hole' hhole' heq
  cases hole with
  | none =>
      cases hole' with
      | none => rfl
      | some rho =>
          have hrho : rho ∈ bcfTruncatedZeros R := by
            simpa [bcfAllDeletedHoles] using hhole'
          exact False.elim ((disks.center_ne_s rho hrho) heq.symm)
  | some rho =>
      cases hole' with
      | none =>
          have hrho : rho ∈ bcfTruncatedZeros R := by
            simpa [bcfAllDeletedHoles] using hhole
          exact False.elim ((disks.center_ne_s rho hrho) heq)
      | some rho' =>
          exact congrArg some (by simpa only [bcfDeletedHoleCenter] using heq)

/-- Every BCF deleted center belongs to the finite center set from which the
axis cuts are constructed. -/
theorem mem_bcfAllDeletedCenters
    (s : ℂ) (R : ℝ) {hole : Option ℂ}
    (hhole : hole ∈ bcfAllDeletedHoles R) :
    bcfDeletedHoleCenter s hole ∈ bcfAllDeletedCenters s R :=
  Finset.mem_image.mpr ⟨hole, hhole, rfl⟩

/-- Every selected BCF axis cut avoids every main-pole or truncated-zero
center. -/
theorem bcfAllDeletedAxisCuts_avoids
    (s : ℂ) (R : ℝ) {cut : AxisCut}
    (hcut : cut ∈ bcfAllDeletedAxisCuts s R) {hole : Option ℂ}
    (hhole : hole ∈ bcfAllDeletedHoles R) :
    cut.Avoids (bcfDeletedHoleCenter s hole) := by
  exact allAxisCuts_avoids (bcfAllDeletedCenters s R) hcut _
    (mem_bcfAllDeletedCenters s R hhole)

/-- Each BCF deleted center has a positive disk that avoids all the selected
axis cuts.  It is the clearance input used before shrinking the actual pole
disks into individual grid cells. -/
theorem exists_pos_radius_bcfDeletedHole_avoids_allAxisCuts
    (s : ℂ) (R : ℝ) {hole : Option ℂ}
    (hhole : hole ∈ bcfAllDeletedHoles R) :
    ∃ r : ℝ, 0 < r ∧
      ∀ cut ∈ bcfAllDeletedAxisCuts s R,
        ∀ z ∈ closedBall (bcfDeletedHoleCenter s hole) r,
          cut.Avoids z := by
  exact exists_pos_radius_avoids_allAxisCuts (bcfAllDeletedCenters s R)
    (mem_bcfAllDeletedCenters s R hhole)

/-- Two distinct BCF deleted holes are separated by one of the selected axis
cuts. -/
theorem exists_bcfAllDeletedAxisCut_separating
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R)
    {hole hole' : Option ℂ}
    (hhole : hole ∈ bcfAllDeletedHoles R)
    (hhole' : hole' ∈ bcfAllDeletedHoles R) (hne : hole ≠ hole') :
    ∃ cut ∈ bcfAllDeletedAxisCuts s R,
      cut.Separates (bcfDeletedHoleCenter s hole) (bcfDeletedHoleCenter s hole') := by
  apply exists_allAxisCut_separating (bcfAllDeletedCenters s R)
    (mem_bcfAllDeletedCenters s R hhole)
    (mem_bcfAllDeletedCenters s R hhole')
  intro hcenter
  exact hne (bcfDeletedHoleCenter_injectiveOn disks hhole hhole' hcenter)

/-- The zero disks can be uniformly shrunk so that every shrunken closed disk
avoids every selected BCF axis cut.  Since `BCFDeletedDiskFamily.scale`
preserves the residue boundary sum, choosing this scale loses no contour
contribution. -/
theorem exists_bcfDeletedDiskScale_avoids_allAxisCuts
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      ∀ rho ∈ bcfTruncatedZeros R, ∀ cut ∈ bcfAllDeletedAxisCuts s R,
        ∀ z ∈ closedBall rho (q * disks.radius rho), cut.Avoids z := by
  classical
  let clearance : ℂ → ℝ := fun rho =>
    if hrho : rho ∈ bcfTruncatedZeros R then
      Classical.choose (exists_pos_radius_bcfDeletedHole_avoids_allAxisCuts s R
        (hole := some rho) (by simpa [bcfAllDeletedHoles] using hrho))
    else 1
  have hclearance : ∀ rho ∈ bcfTruncatedZeros R,
      0 < clearance rho ∧
        ∀ cut ∈ bcfAllDeletedAxisCuts s R,
          ∀ z ∈ closedBall rho (clearance rho), cut.Avoids z := by
    intro rho hrho
    simp only [clearance, dif_pos hrho]
    simpa only [bcfDeletedHoleCenter] using
      Classical.choose_spec (exists_pos_radius_bcfDeletedHole_avoids_allAxisCuts s R
        (hole := some rho) (by simpa [bcfAllDeletedHoles] using hrho))
  obtain ⟨q, hq, hq_one, hq_bound⟩ :=
    exists_pos_le_one_forall_mul_lt (bcfTruncatedZeros R) disks.radius clearance
      disks.radius_pos (fun rho hrho => (hclearance rho hrho).1)
  refine ⟨q, hq, hq_one, ?_⟩
  intro rho hrho cut hcut z hz
  exact (hclearance rho hrho).2 cut hcut z
    (Metric.closedBall_subset_closedBall (hq_bound rho hrho).le hz)

/-- The regular BCF main-pole disk can simultaneously be chosen zero-free,
away from `1`, disjoint from all zero disks, and clear of every selected axis
cut. -/
theorem exists_bcfShiftedMainPoleRadius_disjoint_from_deletedDisks_and_axisCuts
    {N : ℕ} {s : ℂ} {R : ℝ} (disks : BCFDeletedDiskFamily N s R)
    (hs_one : s ≠ 1) (hs_zero : riemannZeta s ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (∀ u ∈ closedBall s r, u ≠ 1) ∧
      (∀ u ∈ closedBall s r, riemannZeta u ≠ 0) ∧
      (∀ rho ∈ bcfTruncatedZeros R,
        Disjoint (closedBall s r) (closedBall rho (disks.radius rho))) ∧
      (∀ cut ∈ bcfAllDeletedAxisCuts s R,
        ∀ u ∈ closedBall s r, cut.Avoids u) := by
  obtain ⟨r₀, hr₀, hone, hzero, hdisj⟩ :=
    exists_bcfShiftedMainPoleRadius_disjoint_from_deletedDisks disks hs_one hs_zero
  obtain ⟨r₁, hr₁, hcuts⟩ :=
    exists_pos_radius_bcfDeletedHole_avoids_allAxisCuts s R
      (hole := none) (by simp [bcfAllDeletedHoles])
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact hone u (Metric.closedBall_subset_closedBall (min_le_left _ _) hu)
  · intro u hu
    exact hzero u (Metric.closedBall_subset_closedBall (min_le_left _ _) hu)
  · intro rho hrho
    apply Disjoint.mono (Metric.closedBall_subset_closedBall (min_le_left _ _)) (by rfl)
    exact hdisj rho hrho
  · intro cut hcut u hu
    exact hcuts cut hcut u (Metric.closedBall_subset_closedBall (min_le_right _ _) hu)

/-- The generic finite-hole circle sum is exactly the BCF local boundary:
the main-pole circle followed by the truncated nontrivial-zero circles. -/
theorem sum_circleIntegral_bcfAllDeletedHoles_eq_localDeletedBoundary
    (N : ℕ) (s : ℂ) (R mainRadius : ℝ)
    (disks : BCFDeletedDiskFamily N s R) :
    (∑ hole ∈ bcfAllDeletedHoles R,
      ∮ u in C(bcfDeletedHoleCenter s hole,
        bcfDeletedHoleRadius mainRadius disks hole), bcfShiftedZeroKernel N s u) =
      bcfLocalDeletedBoundaryIntegral N s R mainRadius disks := by
  classical
  simp [bcfAllDeletedHoles, bcfDeletedHoleCenter, bcfDeletedHoleRadius,
    bcfLocalDeletedBoundaryIntegral, bcfDeletedDiskBoundaryIntegral]

/-- The generic finite deleted-rectangle witness, specialized to the shifted
BCF kernel and to the main pole plus the truncated nontrivial-zero disks. -/
abbrev BCFDeletedRectangleCauchyGoursatWitness
    (N : ℕ) (s : ℂ) (R mainRadius : ℝ)
    (disks : BCFDeletedDiskFamily N s R) {z w : ℂ}
    (S : RectangleSubdivision (bcfShiftedZeroKernel N s) z w) :=
  FiniteDeletedRectangleCauchyGoursatWitness S (bcfAllDeletedHoles R)
    (bcfDeletedHoleCenter s) (bcfDeletedHoleRadius mainRadius disks)

/-- A constructed finite BCF deleted-rectangle witness proves the exact
outer-boundary deformation required by the BCF Lemma 2 assembly. -/
theorem bcfOuterBoundaryDeformation_of_finite_deleted_rectangle_witness
    (N : ℕ) (s : ℂ) (R mainRadius : ℝ)
    (disks : BCFDeletedDiskFamily N s R) {z w : ℂ}
    (S : RectangleSubdivision (bcfShiftedZeroKernel N s) z w)
    (W : BCFDeletedRectangleCauchyGoursatWitness N s R mainRadius disks S) :
    BCFOuterBoundaryDeformation N s R mainRadius disks z w := by
  unfold BCFOuterBoundaryDeformation
  calc
    bcfShiftedRectangleBoundaryIntegral N s z w =
        rectangleBoundaryIntegral (bcfShiftedZeroKernel N s) z w :=
      bcfShiftedRectangleBoundaryIntegral_eq_rectangleBoundaryIntegral_shiftedZeroKernel N s z w
    _ = ∑ hole ∈ bcfAllDeletedHoles R,
        ∮ u in C(bcfDeletedHoleCenter s hole,
          bcfDeletedHoleRadius mainRadius disks hole), bcfShiftedZeroKernel N s u :=
      finite_deleted_rectangle_cauchy_goursat S (bcfAllDeletedHoles R)
        (bcfDeletedHoleCenter s) (bcfDeletedHoleRadius mainRadius disks) W
    _ = bcfLocalDeletedBoundaryIntegral N s R mainRadius disks :=
      sum_circleIntegral_bcfAllDeletedHoles_eq_localDeletedBoundary N s R mainRadius disks

/-- After Perron normalization, a concrete finite BCF deleted-rectangle
witness gives the main term plus the finite nontrivial-zero residue sum. -/
theorem normalized_bcfShiftedRectangleBoundaryIntegral_eq_main_add_nontrivial_of_witness
    {N : ℕ} {s : ℂ} {R mainRadius : ℝ}
    (disks : BCFDeletedDiskFamily N s R) {z w : ℂ}
    (S : RectangleSubdivision (bcfShiftedZeroKernel N s) z w)
    (W : BCFDeletedRectangleCauchyGoursatWitness N s R mainRadius disks S)
    (hN : N ≠ 0) (hlog : (Real.log N : ℂ) ≠ 0) (hmainRadius : 0 < mainRadius)
    (hone : ∀ u ∈ closedBall s mainRadius, u ≠ 1)
    (hzero : ∀ u ∈ closedBall s mainRadius, riemannZeta u ≠ 0) :
    (Real.log N : ℂ)⁻¹ * (2 * Real.pi * I)⁻¹ *
      bcfShiftedRectangleBoundaryIntegral N s z w =
        bcfLemma2MainTerm N s +
          (Real.log N : ℂ)⁻¹ * bcfTruncatedSimpleZeroResidueSum N s R := by
  apply BCFOuterBoundaryDeformation.normalized_eq_main_add_nontrivial
    disks hN hlog hmainRadius hone hzero
  exact bcfOuterBoundaryDeformation_of_finite_deleted_rectangle_witness
    N s R mainRadius disks S W

end

end NBMellinTools.H15BCF
