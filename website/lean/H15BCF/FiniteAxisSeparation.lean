/-
Copyright (c) 2026 Xavier Fresquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Fresquet
-/
import NBMellinTools.H15BCF.FiniteDeletedRectangle

/-!
# Finite axis separation for deleted-disk centers

A finite set of distinct points in the complex plane can be separated by
finitely many vertical and horizontal lines which pass through none of the
points.  The lines are chosen pairwise, then collected into one finite set.

For BCF this is the geometric first step: after the lines are chosen, the
deleted disks can be uniformly shrunk below their finite distance to the
lines.  The present file proves the point-level separation statement; the
subsequent disk-clearance and analytic contour facts remain separate work.
-/

namespace NBMellinTools.H15BCF

noncomputable section

/-- The orientation of an axis-aligned separating line. -/
inductive AxisCutOrientation
  | vertical
  | horizontal
  deriving DecidableEq

/-- An axis-aligned line, represented by its orientation and real coordinate. -/
structure AxisCut where
  orientation : AxisCutOrientation
  coordinate : ℝ
  deriving DecidableEq

/-- A center does not lie on an axis cut. -/
def AxisCut.Avoids (cut : AxisCut) (z : ℂ) : Prop :=
  match cut.orientation with
  | .vertical => z.re ≠ cut.coordinate
  | .horizontal => z.im ≠ cut.coordinate

/-- An axis cut puts two centers on strictly opposite sides. -/
def AxisCut.Separates (cut : AxisCut) (z w : ℂ) : Prop :=
  match cut.orientation with
  | .vertical =>
      (z.re < cut.coordinate ∧ cut.coordinate < w.re) ∨
        (w.re < cut.coordinate ∧ cut.coordinate < z.re)
  | .horizontal =>
      (z.im < cut.coordinate ∧ cut.coordinate < w.im) ∨
        (w.im < cut.coordinate ∧ cut.coordinate < z.im)

/-- The perpendicular distance from a point to an axis cut. -/
def AxisCut.perpendicularDistance (cut : AxisCut) (z : ℂ) : ℝ :=
  match cut.orientation with
  | .vertical => |z.re - cut.coordinate|
  | .horizontal => |z.im - cut.coordinate|

/-- A center avoiding a cut has strictly positive perpendicular distance from
that cut. -/
theorem AxisCut.perpendicularDistance_pos
    {cut : AxisCut} {z : ℂ} (h : cut.Avoids z) :
    0 < cut.perpendicularDistance z := by
  rcases cut with ⟨orientation, coordinate⟩
  cases orientation with
  | vertical =>
      exact abs_pos.mpr (sub_ne_zero.mpr h)
  | horizontal =>
      exact abs_pos.mpr (sub_ne_zero.mpr h)

/-- A disk whose radius is smaller than the perpendicular distance to an axis
cut lies wholly off that cut. -/
theorem AxisCut.avoids_closedBall
    (cut : AxisCut) (c : ℂ) {r : ℝ}
    (hr : r < cut.perpendicularDistance c) :
    ∀ z ∈ Metric.closedBall c r, cut.Avoids z := by
  rcases cut with ⟨orientation, coordinate⟩
  cases orientation with
  | vertical =>
      intro z hz hz_on_cut
      apply (not_le_of_gt hr)
      calc
        |c.re - coordinate| = |(c - z).re| := by simp [hz_on_cut]
        _ ≤ ‖c - z‖ := Complex.abs_re_le_norm _
        _ = dist z c := by rw [dist_comm, dist_eq_norm]
        _ ≤ r := Metric.mem_closedBall.mp hz
  | horizontal =>
      intro z hz hz_on_cut
      apply (not_le_of_gt hr)
      calc
        |c.im - coordinate| = |(c - z).im| := by simp [hz_on_cut]
        _ ≤ ‖c - z‖ := Complex.abs_im_le_norm _
        _ = dist z c := by rw [dist_comm, dist_eq_norm]
        _ ≤ r := Metric.mem_closedBall.mp hz

/-- A nonempty open real interval contains a point outside any prescribed
finite set. -/
theorem exists_real_between_not_mem_finset
    (a b : ℝ) (hab : a < b) (forbidden : Finset ℝ) :
    ∃ c : ℝ, a < c ∧ c < b ∧ c ∉ forbidden := by
  obtain ⟨c, hc, hc_forbidden⟩ :=
    (Set.Ioo_infinite hab).exists_notMem_finset forbidden
  exact ⟨c, hc.1, hc.2, hc_forbidden⟩

/-- Any two distinct points can be separated by a vertical or horizontal line
which avoids an arbitrary finite collection of centers. -/
theorem exists_axisCut_avoiding_finset_separating
    (centers : Finset ℂ) {z w : ℂ} (hzw : z ≠ w) :
    ∃ cut : AxisCut,
      (∀ c ∈ centers, cut.Avoids c) ∧ cut.Separates z w := by
  classical
  by_cases hre : z.re = w.re
  · have him : z.im ≠ w.im := by
      intro him
      exact hzw (Complex.ext hre him)
    rcases lt_or_gt_of_ne him with him_lt | him_gt
    · obtain ⟨v, hzv, hvw, hv_not_mem⟩ :=
        exists_real_between_not_mem_finset z.im w.im him_lt (centers.image Complex.im)
      refine ⟨⟨.horizontal, v⟩, ?_, Or.inl ⟨hzv, hvw⟩⟩
      intro c hc hc_eq
      apply hv_not_mem
      exact Finset.mem_image.mpr ⟨c, hc, hc_eq⟩
    · obtain ⟨v, hwv, hvz, hv_not_mem⟩ :=
        exists_real_between_not_mem_finset w.im z.im him_gt (centers.image Complex.im)
      refine ⟨⟨.horizontal, v⟩, ?_, Or.inr ⟨hwv, hvz⟩⟩
      intro c hc hc_eq
      apply hv_not_mem
      exact Finset.mem_image.mpr ⟨c, hc, hc_eq⟩
  · rcases lt_or_gt_of_ne hre with hre_lt | hre_gt
    · obtain ⟨u, hzu, huw, hu_not_mem⟩ :=
        exists_real_between_not_mem_finset z.re w.re hre_lt (centers.image Complex.re)
      refine ⟨⟨.vertical, u⟩, ?_, Or.inl ⟨hzu, huw⟩⟩
      intro c hc hc_eq
      apply hu_not_mem
      exact Finset.mem_image.mpr ⟨c, hc, hc_eq⟩
    · obtain ⟨u, hwu, huz, hu_not_mem⟩ :=
        exists_real_between_not_mem_finset w.re z.re hre_gt (centers.image Complex.re)
      refine ⟨⟨.vertical, u⟩, ?_, Or.inr ⟨hwu, huz⟩⟩
      intro c hc hc_eq
      apply hu_not_mem
      exact Finset.mem_image.mpr ⟨c, hc, hc_eq⟩

/-- A chosen separating line for two centers.  The value for equal centers is
irrelevant and is excluded when building `allAxisCuts`. -/
noncomputable def axisCutFor (centers : Finset ℂ) (z w : ℂ) : AxisCut :=
  if hzw : z = w then ⟨.vertical, 0⟩ else
    Classical.choose (exists_axisCut_avoiding_finset_separating centers hzw)

/-- The chosen cut avoids every center and separates its distinct input pair. -/
theorem axisCutFor_spec
    (centers : Finset ℂ) {z w : ℂ} (hzw : z ≠ w) :
    (∀ c ∈ centers, (axisCutFor centers z w).Avoids c) ∧
      (axisCutFor centers z w).Separates z w := by
  rw [axisCutFor, dif_neg hzw]
  exact Classical.choose_spec (exists_axisCut_avoiding_finset_separating centers hzw)

/-- The finite collection of cuts chosen for all ordered distinct pairs of
centers. -/
noncomputable def allAxisCuts (centers : Finset ℂ) : Finset AxisCut :=
  ((centers ×ˢ centers).filter fun pair => pair.1 ≠ pair.2).image
    fun pair => axisCutFor centers pair.1 pair.2

/-- Every selected cut avoids every center in the finite collection. -/
theorem allAxisCuts_avoids
    (centers : Finset ℂ) {cut : AxisCut} (hcut : cut ∈ allAxisCuts centers) :
    ∀ c ∈ centers, cut.Avoids c := by
  classical
  rw [allAxisCuts] at hcut
  rcases Finset.mem_image.mp hcut with ⟨pair, hpair, rfl⟩
  have hne : pair.1 ≠ pair.2 := (Finset.mem_filter.mp hpair).2
  exact (axisCutFor_spec centers hne).1

/-- Distinct members of a finite center set are separated by one of the
selected finitely many axis cuts. -/
theorem exists_allAxisCut_separating
    (centers : Finset ℂ) {z w : ℂ}
    (hz : z ∈ centers) (hw : w ∈ centers) (hzw : z ≠ w) :
    ∃ cut ∈ allAxisCuts centers, cut.Separates z w := by
  classical
  refine ⟨axisCutFor centers z w, ?_, (axisCutFor_spec centers hzw).2⟩
  rw [allAxisCuts, Finset.mem_image]
  refine ⟨(z, w), ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz, hw⟩, hzw⟩

/-- A point avoiding finitely many axis cuts has a positive disk avoiding all
of them simultaneously. -/
theorem exists_pos_radius_avoids_finset_axisCuts
    (c : ℂ) (cuts : Finset AxisCut)
    (havoid : ∀ cut ∈ cuts, cut.Avoids c) :
    ∃ r : ℝ, 0 < r ∧
      ∀ cut ∈ cuts, ∀ z ∈ Metric.closedBall c r, cut.Avoids z := by
  classical
  induction cuts using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro cut hcut
      simp at hcut
  | @insert cut cuts hcut ih =>
      have havoid_tail : ∀ other ∈ cuts, other.Avoids c :=
        fun other hother => havoid other (by simp [hother])
      obtain ⟨r, hr, hr_avoids⟩ := ih havoid_tail
      have hcut_avoids : cut.Avoids c := havoid cut (by simp)
      let δ : ℝ := min r (cut.perpendicularDistance c / 2)
      have hδ : 0 < δ := by
        apply lt_min hr
        exact half_pos (cut.perpendicularDistance_pos hcut_avoids)
      refine ⟨δ, hδ, ?_⟩
      intro other hother z hz
      rcases Finset.mem_insert.mp hother with hother | hother
      · subst other
        refine AxisCut.avoids_closedBall _ c ?_ z hz
        calc
          δ ≤ cut.perpendicularDistance c / 2 := min_le_right _ _
          _ < cut.perpendicularDistance c :=
            half_lt_self (cut.perpendicularDistance_pos hcut_avoids)
      · apply hr_avoids other hother z
        exact Metric.closedBall_subset_closedBall (min_le_left _ _) hz

/-- The cuts constructed from a finite center set admit a positive local
clearance disk around each one of its centers. -/
theorem exists_pos_radius_avoids_allAxisCuts
    (centers : Finset ℂ) {c : ℂ} (hc : c ∈ centers) :
    ∃ r : ℝ, 0 < r ∧
      ∀ cut ∈ allAxisCuts centers, ∀ z ∈ Metric.closedBall c r, cut.Avoids z :=
  exists_pos_radius_avoids_finset_axisCuts c (allAxisCuts centers)
    (fun _ hcut => allAxisCuts_avoids centers hcut c hc)

/-- Finitely many positive multiplicative radii admit one positive scale at
most one that lies strictly below all prescribed positive clearances. -/
theorem exists_pos_le_one_forall_mul_lt
    {α : Type*} (points : Finset α)
    (radius clearance : α → ℝ)
    (hradius : ∀ x ∈ points, 0 < radius x)
    (hclearance : ∀ x ∈ points, 0 < clearance x) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧
      ∀ x ∈ points, q * radius x < clearance x := by
  classical
  induction points using Finset.induction_on with
  | empty =>
      refine ⟨1, zero_lt_one, le_rfl, ?_⟩
      intro x hx
      simp at hx
  | @insert a points hpoint ih =>
      have hradius_tail : ∀ x ∈ points, 0 < radius x :=
        fun x hx => hradius x (by simp [hx])
      have hclearance_tail : ∀ x ∈ points, 0 < clearance x :=
        fun x hx => hclearance x (by simp [hx])
      obtain ⟨q, hq, hq_one, hq_bound⟩ := ih hradius_tail hclearance_tail
      let q' : ℝ := min q (clearance a / (2 * radius a))
      have hdenom : 0 < 2 * radius a :=
        mul_pos (by norm_num) (hradius a (by simp))
      have hq' : 0 < q' := by
        apply lt_min hq
        exact div_pos (hclearance a (by simp)) hdenom
      refine ⟨q', hq', le_trans (min_le_left _ _) hq_one, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · calc
          q' * radius y ≤
              (clearance y / (2 * radius y)) * radius y :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (hradius y (by simp)).le
          _ = clearance y / 2 := by
            field_simp [ne_of_gt (hradius y (by simp))]
          _ < clearance y := half_lt_self (hclearance y (by simp))
      · exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right (min_le_left _ _) (hradius y (by simp [hy])).le)
          (hq_bound y hy)

end

end NBMellinTools.H15BCF
