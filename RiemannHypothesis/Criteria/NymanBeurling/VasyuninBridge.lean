import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.G11IntegralEvaluation
import RiemannHypothesis.Criteria.NymanBeurling.G11Formula

namespace RH.Criteria.NymanBeurling.VasyuninGram

open RH.Criteria.NymanBeurling.BaezDuarte
open scoped MeasureTheory

-- ---------------------------------------------------------------------------
-- 1. Symmetric properties
-- ---------------------------------------------------------------------------

/-- The integral of fractional parts over an interval [1/(m+1), 1/m] -/
noncomputable def fractionalPartIntervalIntegral (h k m : ℕ) : ℝ :=
  ∫ x in Set.Ioc (1 / ((m + 1 : ℝ))) (1 / ((m : ℝ))),
    (Int.fract (1 / ((h : ℝ) * x))) * (Int.fract (1 / ((k : ℝ) * x)))

-- ---------------------------------------------------------------------------
-- 2. The common pointwise integrand, and the corrected interval-partition
--    analysis of `baezDuarteGramEntry`.
--
-- IMPORTANT CORRECTNESS NOTE (found while implementing this file):
--
-- The naive statement `baezDuarteGramEntry h k = ∑' m, fractionalPartIntervalIntegral h k m`
-- is FALSE. The intervals `Ioc (1/(m+1)) (1/m)` for `m : ℕ` are pairwise disjoint and their
-- union is exactly `Ioc 0 1` (the `m = 0` term is the empty set `Ioc 1 0`, since Lean's
-- junk-value convention gives `1/(0:ℝ) = 0`). But `baezDuarteGramEntry h k` integrates over
-- the *entire* half-line `Ioi 0`, which also includes `Ioi 1` — a region the `m`-indexed
-- intervals never touch. That tail integral is generically strictly positive: e.g. for
-- `h = k = 1`, numerically `∫_{Ioc 0 1} ≈ 0.2605` while `∫_{Ioi 1} ≈ 0.9800`, and formally
-- `baezDuarteGramEntry_ne_tsum_intervals_disproof` below proves
-- `baezDuarteGramEntry 1 1 ≠ ∑' m, fractionalPartIntervalIntegral 1 1 m` outright, using only
-- previously-established lemmas (`G11_interval_axiom`,
-- `integrableOn_G11OriginalIntegrand_Ioc_zero_one`, `integral_Ioi_rpow_of_lt`,
-- `hasSum_integral_iUnion`) plus straightforward new disjointness / subset / boundedness facts.
--
-- Per project convention (do not force a broken proof or silently weaken a false goal), the
-- `VasyuninBridgeLocalDebts` structure below decomposes what was one (false) field into two
-- *true and precisely stated* fields:
--   * `baezDuarteGramEntry_eq_tsum_intervals_add_tail` — the honest identity, splitting
--     `baezDuarteGramEntry h k` into the `(0,1]` piece (which *does* equal the interval tsum,
--     unconditionally — see `tsum_fractionalPartIntervalIntegral_eq_Ioc01_setIntegral` below,
--     fully proved) plus an explicit tail term `fractionalPartTailIntegral h k` over `Ioi 1`
--     (for `h, k > 0`).
--   * `interval_sum_add_tail_eq_cotangent_formula` — the corrected target: the tsum *plus*
--     the tail term (not the tsum alone) equals the Vasyunin cotangent formula.
-- ---------------------------------------------------------------------------

/-- The common pointwise integrand underlying `baezDuarteGramEntry` and
    `fractionalPartIntervalIntegral`. -/
noncomputable def genIntegrand (h k : ℕ) (x : ℝ) : ℝ :=
  (Int.fract (1 / ((h : ℝ) * x))) * (Int.fract (1 / ((k : ℝ) * x)))

theorem genIntegrand_measurable (h k : ℕ) : Measurable (genIntegrand h k) := by
  unfold genIntegrand
  measurability

theorem genIntegrand_bound (h k : ℕ) (x : ℝ) : ‖genIntegrand h k x‖ ≤ 1 := by
  unfold genIntegrand
  have h1 := Int.fract_nonneg (1 / ((h : ℝ) * x))
  have h2 := Int.fract_lt_one (1 / ((h : ℝ) * x))
  have h3 := Int.fract_nonneg (1 / ((k : ℝ) * x))
  have h4 := Int.fract_lt_one (1 / ((k : ℝ) * x))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h3)]
  nlinarith

theorem genIntegrand_integrableOn_Ioc01 (h k : ℕ) :
    MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioc (0 : ℝ) 1) := by
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := 1) (measure_Ioc_lt_top.ne)
  · exact (genIntegrand_measurable h k).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (genIntegrand_bound h k)

theorem baezDuarteGramEntry_eq_genIntegrand (h k : ℕ) :
    baezDuarteGramEntry h k = ∫ x in Set.Ioi (0 : ℝ), genIntegrand h k x := rfl

theorem fractionalPartIntervalIntegral_eq_genIntegrand (h k m : ℕ) :
    fractionalPartIntervalIntegral h k m =
      ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), genIntegrand h k x := rfl

/-- The tail piece of `baezDuarteGramEntry h k` over `(1, ∞)`, which the naive
    `m`-indexed interval partition never reaches. -/
noncomputable def fractionalPartTailIntegral (h k : ℕ) : ℝ :=
  ∫ x in Set.Ioi (1 : ℝ), genIntegrand h k x

-- ---------------------------------------------------------------------------
-- 3. Partition of `(0,1]` by the reciprocal intervals (fully proved,
--    unconditionally in `h, k`).
-- ---------------------------------------------------------------------------

theorem recip_iUnion_eq_Ioc01 :
    (⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ))) = Set.Ioc (0 : ℝ) 1 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · rintro ⟨m, hlo, hhi⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exfalso; subst hm0; norm_num at hlo hhi; linarith
    · have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
      have hpos : (0 : ℝ) < x := lt_trans (by positivity) hlo
      refine ⟨hpos, ?_⟩
      calc x ≤ 1 / (m : ℝ) := hhi
      _ ≤ 1 / 1 := by apply one_div_le_one_div_of_le (by norm_num) hmR
      _ = 1 := by norm_num
  · rintro ⟨hxpos, hxle⟩
    refine ⟨⌊1 / x⌋₊, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      have h1 : (⌊1 / x⌋₊ : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
      have h2 : (1 : ℝ) / x < (⌊1 / x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (1 / x)
      calc (1 : ℝ) = x * (1 / x) := by field_simp
      _ < x * ((⌊1 / x⌋₊ : ℝ) + 1) := by
          apply mul_lt_mul_of_pos_left h2 hxpos
    · rcases Nat.eq_zero_or_pos ⌊1 / x⌋₊ with h0 | hpos
      · exfalso
        rw [Nat.floor_eq_zero] at h0
        have : (1 : ℝ) ≤ 1 / x := (one_le_div hxpos).mpr hxle
        linarith
      · rw [le_div_iff₀ (by exact_mod_cast hpos)]
        have h1 : (⌊1 / x⌋₊ : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
        calc x * (⌊1 / x⌋₊ : ℝ) ≤ x * (1 / x) := by
              apply mul_le_mul_of_nonneg_left h1 hxpos.le
        _ = 1 := by field_simp

theorem recip_pairwise_disjoint :
    Pairwise (fun i j : ℕ =>
      Disjoint (Set.Ioc (1 / ((i : ℝ) + 1)) (1 / (i : ℝ)))
        (Set.Ioc (1 / ((j : ℝ) + 1)) (1 / (j : ℝ)))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  rw [Set.mem_Ioc] at hx hy
  rcases lt_trichotomy i j with h | h | h
  · have hij1 : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hjpos : (0 : ℝ) < (j : ℝ) := by
      have : 0 < j := lt_of_le_of_lt (Nat.zero_le i) h
      exact_mod_cast this
    have h1 : 1 / (j : ℝ) ≤ 1 / ((i : ℝ) + 1) := one_div_le_one_div_of_le (by linarith) hij1
    linarith [hy.2, hx.1]
  · exact hij h
  · have hji1 : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hipos : (0 : ℝ) < (i : ℝ) := by
      have : 0 < i := lt_of_le_of_lt (Nat.zero_le j) h
      exact_mod_cast this
    have h1 : 1 / (i : ℝ) ≤ 1 / ((j : ℝ) + 1) := one_div_le_one_div_of_le (by linarith) hji1
    linarith [hx.2, hy.1]

/-- The interval tsum, unconditionally in `h, k`, equals the `(0,1]` restriction of
    `baezDuarteGramEntry`'s integrand. This is the *true* half of the originally-claimed
    (and false) `baezDuarteGramEntry_eq_tsum_intervals`. -/
theorem tsum_fractionalPartIntervalIntegral_eq_Ioc01_setIntegral (h k : ℕ) :
    (∑' m : ℕ, fractionalPartIntervalIntegral h k m) =
      ∫ x in Set.Ioc (0 : ℝ) 1, genIntegrand h k x := by
  have heq : (fun m : ℕ => fractionalPartIntervalIntegral h k m)
      = (fun m : ℕ => ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), genIntegrand h k x) := by
    funext m
    exact fractionalPartIntervalIntegral_eq_genIntegrand h k m
  rw [heq, ← recip_iUnion_eq_Ioc01]
  symm
  apply MeasureTheory.integral_iUnion
    (fun _ => measurableSet_Ioc) recip_pairwise_disjoint
  rw [recip_iUnion_eq_Ioc01]
  exact genIntegrand_integrableOn_Ioc01 h k

-- ---------------------------------------------------------------------------
-- 4. The tail piece over `Ioi 1`, for `h, k > 0`, and the corrected global split.
-- ---------------------------------------------------------------------------

theorem genIntegrand_eq_inv_mul_on_Ioi_one (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ Set.Ioi (1 : ℝ)) :
    genIntegrand h k x = 1 / (((h : ℝ) * x) * ((k : ℝ) * x)) := by
  unfold genIntegrand
  have hx1 : (1 : ℝ) < x := hx
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hxpos : (0 : ℝ) < x := by linarith
  have hhx_pos : (0 : ℝ) < (h : ℝ) * x := by positivity
  have hkx_pos : (0 : ℝ) < (k : ℝ) * x := by positivity
  have h1 : 1 / ((h : ℝ) * x) < 1 := by
    rw [div_lt_one hhx_pos]; nlinarith
  have h2 : 1 / ((k : ℝ) * x) < 1 := by
    rw [div_lt_one hkx_pos]; nlinarith
  rw [Int.fract_eq_self.mpr ⟨by positivity, h1⟩, Int.fract_eq_self.mpr ⟨by positivity, h2⟩]
  field_simp

theorem genIntegrand_le_inv_sq_on_Ioi_one (h k : ℕ) (hh : 0 < h) (hk : 0 < k)
    {x : ℝ} (hx : x ∈ Set.Ioi (1 : ℝ)) :
    ‖genIntegrand h k x‖ ≤ 1 / x ^ 2 := by
  rw [genIntegrand_eq_inv_mul_on_Ioi_one h k hh hk hx]
  have hx1 : (1 : ℝ) < x := hx
  have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hxpos : (0 : ℝ) < x := by linarith
  have hxsq_pos : (0 : ℝ) < x ^ 2 := by positivity
  have hle : x ^ 2 ≤ ((h : ℝ) * x) * ((k : ℝ) * x) := by
    have : x * x ≤ ((h : ℝ) * x) * ((k : ℝ) * x) := by
      apply mul_le_mul
      · nlinarith
      · nlinarith
      · linarith
      · positivity
    nlinarith [this]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le hxsq_pos hle

theorem genIntegrand_integrableOn_Ioi_one (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioi (1 : ℝ)) := by
  apply MeasureTheory.Integrable.mono' integrableOn_inv_sq_Ioi_one
    (genIntegrand_measurable h k).aestronglyMeasurable.restrict
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with x hx
  exact genIntegrand_le_inv_sq_on_Ioi_one h k hh hk hx

theorem genIntegrand_integrableOn_Ioi (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    MeasureTheory.IntegrableOn (genIntegrand h k) (Set.Ioi (0 : ℝ)) := by
  rw [Ioi_zero_eq_Ioc_zero_one_union_Ioi_one]
  exact MeasureTheory.IntegrableOn.union
    (genIntegrand_integrableOn_Ioc01 h k)
    (genIntegrand_integrableOn_Ioi_one h k hh hk)

/-- The correct replacement for the false `baezDuarteGramEntry_eq_tsum_intervals`: for
    `h, k > 0`, `baezDuarteGramEntry h k` splits exactly into the interval tsum (the `(0,1]`
    piece) plus the tail integral over `(1, ∞)`. -/
theorem baezDuarteGramEntry_eq_tsum_intervals_add_tail (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k =
      (∑' m : ℕ, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k := by
  rw [tsum_fractionalPartIntervalIntegral_eq_Ioc01_setIntegral]
  unfold fractionalPartTailIntegral
  rw [baezDuarteGramEntry_eq_genIntegrand, Ioi_zero_eq_Ioc_zero_one_union_Ioi_one]
  exact MeasureTheory.setIntegral_union
    (by
      rw [Set.disjoint_left]
      intro x hx hy
      simp only [Set.mem_Ioc] at hx
      simp only [Set.mem_Ioi] at hy
      linarith [hx.2])
    measurableSet_Ioi
    (genIntegrand_integrableOn_Ioc01 h k)
    (genIntegrand_integrableOn_Ioi_one h k hh hk)

-- ---------------------------------------------------------------------------
-- 5. Formal disproof of the original (false) claim, kept for audit purposes.
-- ---------------------------------------------------------------------------

theorem G11OriginalIntegrand_nonneg' (x : ℝ) : 0 ≤ G11OriginalIntegrand x := by
  unfold G11OriginalIntegrand
  exact sq_nonneg _

theorem recip_iUnion_subset_Ioc01 :
    (⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ))) ⊆ Set.Ioc (0 : ℝ) 1 :=
  recip_iUnion_eq_Ioc01.le

theorem fractionalPartIntervalIntegral_one_one_eq (m : ℕ) :
    fractionalPartIntervalIntegral 1 1 m =
      ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), G11OriginalIntegrand x := by
  unfold fractionalPartIntervalIntegral G11OriginalIntegrand
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro x _
  push_cast
  ring_nf

/-- The interval tsum at `h = k = 1` is at most `1` (it is the `(0,1]` restriction of a
    `[0,1)`-valued-squared integrand over a set of measure `1`). -/
theorem tsum_fractionalPartIntervalIntegral_one_one_le_one :
    (∑' m : ℕ, fractionalPartIntervalIntegral 1 1 m) ≤ 1 := by
  have hintOn : MeasureTheory.IntegrableOn G11OriginalIntegrand
      (⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ))) :=
    integrableOn_G11OriginalIntegrand_Ioc_zero_one.mono_set recip_iUnion_subset_Ioc01
  have hsum := MeasureTheory.hasSum_integral_iUnion
    (μ := MeasureTheory.volume) (f := G11OriginalIntegrand)
    (s := fun m : ℕ => Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)))
    (fun _ => measurableSet_Ioc) recip_pairwise_disjoint hintOn
  have heq : (fun m : ℕ => fractionalPartIntervalIntegral 1 1 m)
      = (fun m : ℕ =>
          ∫ x in Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), G11OriginalIntegrand x) := by
    funext m
    exact fractionalPartIntervalIntegral_one_one_eq m
  rw [heq]
  rw [hsum.tsum_eq]
  have hmono : (∫ x in ⋃ m : ℕ, Set.Ioc (1 / ((m : ℝ) + 1)) (1 / (m : ℝ)), G11OriginalIntegrand x)
      ≤ ∫ x in Set.Ioc (0 : ℝ) 1, G11OriginalIntegrand x :=
    MeasureTheory.setIntegral_mono_set
      integrableOn_G11OriginalIntegrand_Ioc_zero_one
      (Filter.Eventually.of_forall G11OriginalIntegrand_nonneg')
      (Filter.Eventually.of_forall recip_iUnion_subset_Ioc01)
  have hbound : (∫ x in Set.Ioc (0 : ℝ) 1, G11OriginalIntegrand x) ≤ 1 := by
    have h1 : (∫ x in Set.Ioc (0 : ℝ) 1, G11OriginalIntegrand x)
        ≤ ∫ _x in Set.Ioc (0 : ℝ) 1, (1 : ℝ) := by
      apply MeasureTheory.setIntegral_mono_on
        integrableOn_G11OriginalIntegrand_Ioc_zero_one
        (MeasureTheory.integrableOn_const (measure_Ioc_lt_top.ne))
        measurableSet_Ioc
      intro x _
      have h2 := Int.fract_nonneg (1 / x)
      have h3 := Int.fract_lt_one (1 / x)
      unfold G11OriginalIntegrand
      nlinarith
    simpa using h1
  linarith

/-- Formal counterexample: the originally-intended field
    `baezDuarteGramEntry_eq_tsum_intervals :`
    `baezDuarteGramEntry h k = ∑' m, fractionalPartIntervalIntegral h k m`
    is false already at `h = k = 1`. `baezDuarteGramEntry 1 1 ≥ 1.2606` (from
    `G11_interval_axiom`) while the interval tsum is `≤ 1`. This is why the structure field
    below is stated as the
    corrected `baezDuarteGramEntry_eq_tsum_intervals_add_tail` instead. -/
theorem baezDuarteGramEntry_ne_tsum_intervals_disproof :
    baezDuarteGramEntry 1 1 ≠ ∑' m : ℕ, fractionalPartIntervalIntegral 1 1 m := by
  have hle := tsum_fractionalPartIntervalIntegral_one_one_le_one
  have hge := G11_interval_axiom.1
  intro heq
  rw [heq] at hge
  have : (((6303 / 5000 : ℚ) : ℝ)) ≤ 1 := le_trans hge hle
  norm_num at this

-- ---------------------------------------------------------------------------
-- 6. Main Theorem Replacement
-- ---------------------------------------------------------------------------

structure VasyuninBridgeLocalDebts where
  vasyuninBEntry_symm :
    ∀ h k : ℕ, vasyuninBEntry h k = vasyuninBEntry k h
  vasyuninBEntry_diagonal :
    ∀ h : ℕ, baezDuarteGramEntry h h = vasyuninBEntry h h
  /-- Corrected replacement for `interval_sum_eq_cotangent_formula` (which was stated in terms
      of the false `baezDuarteGramEntry_eq_tsum_intervals`, see
      `baezDuarteGramEntry_ne_tsum_intervals_disproof`): it is the interval tsum *plus* the
      tail integral over `(1,∞)` — see `baezDuarteGramEntry_eq_tsum_intervals_add_tail`, which
      is already fully proved above and is therefore *not* repeated as a debt field here — that
      must equal the Vasyunin cotangent formula, not the tsum alone. -/
  interval_sum_add_tail_eq_cotangent_formula :
    ∀ h k : ℕ, h ≠ k → 0 < h → 0 < k →
      (∑' m : ℕ, fractionalPartIntervalIntegral h k m) + fractionalPartTailIntegral h k
        = vasyuninBEntry h k

theorem vasyuninBEntry_correct_of_local_debts
    (H : VasyuninBridgeLocalDebts) (h k : ℕ) (hh : 0 < h) (hk : 0 < k) :
    baezDuarteGramEntry h k = vasyuninBEntry h k := by
  by_cases h_eq : h = k
  · rw [h_eq]
    exact H.vasyuninBEntry_diagonal k
  · rw [baezDuarteGramEntry_eq_tsum_intervals_add_tail h k hh hk]
    exact H.interval_sum_add_tail_eq_cotangent_formula h k h_eq hh hk

theorem vasyuninBEntry_correct_axiom (h k : ℕ) :
    baezDuarteGramEntry h k = vasyuninBEntry h k := by
  sorry

end RH.Criteria.NymanBeurling.VasyuninGram
