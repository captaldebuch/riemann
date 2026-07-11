import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.H14ZeroFree

/-!
# A1: the Euler–Maclaurin continuation of `ζ` to the right half-plane

Proves, for a natural cutoff `X ≥ 1` and `Re s > 1`,

`ζ(s) = ∑_{n≤X} n^{−s} + X^{1−s}/(s−1) − s·∫_{X}^{∞} {u}·u^{−s−1} du`,

then continues the identity to `Re s > 0` (`s ≠ 1`) by the identity theorem
applied to the pole-removed pair, and derives the three component bounds
needed to inhabit `ZetaRightHalfEulerMaclaurinComponentsAtHeight`.

Route notes (E0 search recorded in project memory: Mathlib has no such
representation): the `Re s > 1` identity is obtained WITHOUT discrete Abel
summation — each tail term is `n^{−s} = s·∫_{Ioi n} u^{−s−1} du`
(`integral_Ioi_cpow_of_lt`), and the tsum–integral swap
(`MeasureTheory.integral_tsum`) converts the tail of the Dirichlet series
into `s·∫_{Ioi X} (⌊u⌋ − X)·u^{−s−1} du`; writing `⌊u⌋ − X = (u − X) − {u}`
splits off the exact pole term.
-/

namespace RH.Criteria.NymanBeurling.H14ZetaEM

open Complex MeasureTheory Set Filter Topology
open scoped Real

/-! ## The fract tail integral -/

/-- The Euler–Maclaurin tail integrand at complex exponent `s`. -/
noncomputable def emTailIntegrand (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- The tail integral `∫_{Ioi X} {u}·u^{−s−1} du`. -/
noncomputable def emTail (s : ℂ) (X : ℝ) : ℂ :=
  ∫ u in Ioi X, emTailIntegrand s u

theorem emTailIntegrand_norm_le {s : ℂ} {u : ℝ} (hu : 1 ≤ u) :
    ‖emTailIntegrand s u‖ ≤ u ^ (-s.re - 1) := by
  have hupos : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  unfold emTailIntegrand
  rw [norm_mul]
  have h1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg u)]
    exact (Int.fract_lt_one u).le
  have h2 : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hupos]
    norm_num
  calc ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖
      ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        apply mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = u ^ (-s.re - 1) := by rw [one_mul, h2]

/-- Measurability of the tail integrand. -/
theorem emTailIntegrand_aestronglyMeasurable (s : ℂ) {X : ℝ} :
    AEStronglyMeasurable (emTailIntegrand s) (volume.restrict (Ioi X)) := by
  apply Measurable.aestronglyMeasurable
  unfold emTailIntegrand
  apply Measurable.mul
  · exact Complex.measurable_ofReal.comp measurable_fract
  · apply Measurable.pow
    · exact Complex.measurable_ofReal
    · exact measurable_const

/-- Integrability of the tail integrand on `Ioi X` for `Re s > 0`, `X ≥ 1`. -/
theorem emTailIntegrand_integrableOn {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 1 ≤ X) :
    IntegrableOn (emTailIntegrand s) (Ioi X) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hmaj : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi X) := by
    apply integrableOn_Ioi_rpow_of_lt _ hXpos
    linarith
  apply Integrable.mono' hmaj (emTailIntegrand_aestronglyMeasurable s)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with u hu
  exact emTailIntegrand_norm_le (le_trans hX (le_of_lt hu))

/-! ## E1: the identity on `Re s > 1` -/

/-- Per-term improper integral: `n^{−s} = s·∫_{Ioi n} u^{−s−1} du` for `Re s > 0`. -/
theorem cpow_neg_eq_mul_integral {s : ℂ} (hs : 0 < s.re) {n : ℝ} (hn : 0 < n) :
    (n : ℂ) ^ (-s) = s * ∫ u in Ioi n, (u : ℂ) ^ (-s - 1) := by
  have ha : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [integral_Ioi_cpow_of_lt ha hn]
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [show -s - 1 + 1 = -s from by ring]
  field_simp

/-- The Dirichlet tail as a tsum: for `Re s > 1` and a natural cutoff `X`,
`ζ(s) − ∑_{n=1}^{X} n^{−s} = ∑'_{n} ((n+X+1 : ℕ))^{−s}`. -/
theorem zeta_sub_partial_eq_tsum_tail {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    riemannZeta s - (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) =
      ∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s) := by
  have hzeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hsummable : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have h0 := Complex.summable_one_div_nat_cpow.mpr hs
    have hcomp := h0.comp_injective (add_left_injective 1)
    apply hcomp.congr
    intro n
    simp only [Function.comp]
    push_cast
    ring_nf
  have hsplit := hsummable.sum_add_tsum_nat_add X
  have hfin : (∑ i ∈ Finset.range X, 1 / ((i : ℂ) + 1) ^ s) =
      ∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s) := by
    rw [show Finset.Icc 1 X = Finset.Ico 1 (X + 1) from by ext n; simp,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.cpow_neg, one_div]
    congr 2
    push_cast
    ring
  have htail : (∑' n : ℕ, 1 / (((n + X : ℕ) : ℂ) + 1) ^ s) =
      ∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s) := by
    apply tsum_congr
    intro n
    rw [Complex.cpow_neg, one_div]
    congr 2
    push_cast
    ring
  rw [hzeta, ← hsplit, hfin, add_sub_cancel_left]
  exact htail

/-! ## E1b: the tsum-integral swap -/

/-- The shifted per-term integrand, as an indicator function on the common base ray. -/
noncomputable def shiftedIndicator (s : ℂ) (X : ℕ) (n : ℕ) : ℝ → ℂ :=
  (Ioi ((n + X + 1 : ℕ) : ℝ)).indicator fun u : ℝ => (u : ℂ) ^ (-s - 1)

theorem shiftedIndicator_integrableOn {s : ℂ} (hs : 0 < s.re) (X : ℕ) (n : ℕ) :
    Integrable (shiftedIndicator s X n) (volume.restrict (Ioi (X : ℝ))) := by
  have hc : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
  have hbase : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Ioi ((n + X + 1 : ℕ) : ℝ)) := by
    have ha : (-s - 1).re < -1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      linarith
    exact integrableOn_Ioi_cpow_of_lt ha hc
  have hXc : (X : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) := by push_cast; linarith
  unfold shiftedIndicator
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioi]
  rw [IntegrableOn, MeasureTheory.Measure.restrict_restrict measurableSet_Ioi,
    Set.Ioi_inter_Ioi, max_eq_left hXc]
  exact hbase

theorem shiftedIndicator_integral_norm {s : ℂ} (hs : 0 < s.re) (X : ℕ) (n : ℕ) :
    (∫ u in Ioi (X : ℝ), ‖shiftedIndicator s X n u‖) =
      ((n + X + 1 : ℕ) : ℝ) ^ (-s.re) / s.re := by
  have hc : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
  have hXc : (X : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hnorm : ∀ u ∈ Ioi ((n + X + 1 : ℕ) : ℝ),
      ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    intro u hu
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans hc hu)]
    norm_num
  calc (∫ u in Ioi (X : ℝ), ‖shiftedIndicator s X n u‖)
      = ∫ u in Ioi ((n + X + 1 : ℕ) : ℝ), ‖(u : ℂ) ^ (-s - 1)‖ := by
        unfold shiftedIndicator
        simp only [norm_indicator_eq_indicator_norm]
        rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
        congr 1
        rw [Set.Ioi_inter_Ioi, max_eq_right hXc]
    _ = ∫ u in Ioi ((n + X + 1 : ℕ) : ℝ), u ^ (-s.re - 1) :=
        setIntegral_congr_fun measurableSet_Ioi hnorm
    _ = ((n + X + 1 : ℕ) : ℝ) ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hc]
        rw [show -s.re - 1 + 1 = -s.re from by ring]
        field_simp

theorem shiftedIndicator_summable_integral_norm {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    Summable fun n : ℕ => ∫ u in Ioi (X : ℝ), ‖shiftedIndicator s X n u‖ := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have h0 : Summable fun n : ℕ => ((n + X + 1 : ℕ) : ℝ) ^ (-s.re) / s.re := by
    apply Summable.div_const
    have h1 := Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)
    have h2 := h1.comp_injective
      (show Function.Injective (fun n : ℕ => n + X + 1) from fun a b hab => by
        simpa using hab)
    apply h2.congr
    intro n
    simp only [Function.comp_apply]
  exact h0.congr fun n => (shiftedIndicator_integral_norm hs0 X n).symm

/-- Pointwise count identity: away from the integers, the sum of the shifted
indicators counts `⌊u⌋₊ − X` copies of `u^{−s−1}`. -/
theorem tsum_shiftedIndicator_eq {s : ℂ} (X : ℕ) {u : ℝ} (hu : (X : ℝ) < u)
    (hnotint : ∀ m : ℕ, u ≠ m) :
    (∑' n : ℕ, shiftedIndicator s X n u) =
      ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hu0 : 0 < u := lt_of_le_of_lt hX0 hu
  have hXfloor : X ≤ ⌊u⌋₊ := Nat.le_floor hu.le
  have hkey : ∀ n : ℕ, shiftedIndicator s X n u =
      if n ∈ Finset.range (⌊u⌋₊ - X) then (u : ℂ) ^ (-s - 1) else 0 := by
    intro n
    unfold shiftedIndicator
    rw [Set.indicator_apply]
    congr 1
    simp only [Finset.mem_range, Set.mem_Ioi, eq_iff_iff]
    constructor
    · intro h
      have hle : (n + X + 1 : ℕ) ≤ ⌊u⌋₊ := Nat.le_floor (le_of_lt h)
      omega
    · intro h
      have hle : (n + X + 1 : ℕ) ≤ ⌊u⌋₊ := by omega
      have h1 : ((n + X + 1 : ℕ) : ℝ) ≤ (⌊u⌋₊ : ℝ) := Nat.cast_le.mpr hle
      have h2 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0.le
      have h3 : (⌊u⌋₊ : ℝ) ≠ u := fun heq => hnotint ⌊u⌋₊ heq.symm
      linarith [lt_of_le_of_ne h2 h3]
  rw [tsum_congr hkey, tsum_eq_sum (f := fun n =>
      if n ∈ Finset.range (⌊u⌋₊ - X) then (u : ℂ) ^ (-s - 1) else 0)
      (s := Finset.range (⌊u⌋₊ - X)) (fun n hn => if_neg hn)]
  rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, Finset.card_range]
  simp [nsmul_eq_mul]

/-- E1b: for `Re s > 1`, the Dirichlet tail equals `s` times the counted integral. -/
theorem tsum_tail_eq_mul_integral_count {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    (∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s)) =
      s * ∫ u in Ioi (X : ℝ), ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hterm : ∀ n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s) =
      s * ∫ u in Ioi (X : ℝ), shiftedIndicator s X n u := by
    intro n
    have hc : (0 : ℝ) < ((n + X + 1 : ℕ) : ℝ) := by positivity
    have hXc : (X : ℝ) ≤ ((n + X + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h1 := cpow_neg_eq_mul_integral hs0 hc
    have h2 : (∫ u in Ioi (X : ℝ), shiftedIndicator s X n u) =
        ∫ u in Ioi ((n + X + 1 : ℕ) : ℝ), (u : ℂ) ^ (-s - 1) := by
      unfold shiftedIndicator
      rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
      congr 1
      rw [Set.Ioi_inter_Ioi, max_eq_right hXc]
    rw [h2, ← h1]
    norm_num
  have hswap : (∑' n : ℕ, ∫ u in Ioi (X : ℝ), shiftedIndicator s X n u) =
      ∫ u in Ioi (X : ℝ), ∑' n : ℕ, shiftedIndicator s X n u := by
    rw [MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n => shiftedIndicator_integrableOn hs0 X n)
      (shiftedIndicator_summable_integral_norm hs X)]
  have hcount : (∫ u in Ioi (X : ℝ), ∑' n : ℕ, shiftedIndicator s X n u) =
      ∫ u in Ioi (X : ℝ), ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    apply MeasureTheory.integral_congr_ae
    have h1 : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (X : ℝ))), u ∈ Ioi (X : ℝ) :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioi
    have hnull : volume (Set.range (Nat.cast : ℕ → ℝ)) = 0 :=
      (Set.countable_range _).measure_zero _
    have h2' : ∀ᵐ u : ℝ ∂volume, u ∉ Set.range (Nat.cast : ℕ → ℝ) := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    have h2 : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi (X : ℝ))),
        u ∉ Set.range (Nat.cast : ℕ → ℝ) :=
      MeasureTheory.ae_restrict_of_ae h2'
    filter_upwards [h1, h2] with u hu hu'
    exact tsum_shiftedIndicator_eq X hu fun m heq => hu' ⟨m, heq.symm⟩
  have hsum : (∑' n : ℕ, ((n + X + 1 : ℕ) : ℂ) ^ (-s)) =
      s * ∑' n : ℕ, ∫ u in Ioi (X : ℝ), shiftedIndicator s X n u := by
    rw [← tsum_mul_left]
    exact tsum_congr hterm
  rw [hsum, hswap, hcount]

/-! ## E1c: splitting off the pole term and assembling the identity -/

/-- For positive real `u`, the natural floor recovers `u − {u}` in `ℂ`. -/
theorem natCast_floor_eq_sub_fract {u : ℝ} (hu : 0 < u) :
    ((⌊u⌋₊ : ℕ) : ℂ) = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by
  have h1 : ((⌊u⌋₊ : ℕ) : ℝ) = u - Int.fract u := by
    rw [Int.self_sub_fract]
    exact_mod_cast Int.natCast_floor_eq_floor hu.le
  calc ((⌊u⌋₊ : ℕ) : ℂ) = (((⌊u⌋₊ : ℕ) : ℝ) : ℂ) := by push_cast; ring
    _ = ((u - Int.fract u : ℝ) : ℂ) := by rw [h1]
    _ = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by push_cast; ring

/-- The linear piece of the counted integrand is integrable for `Re s > 1`. -/
theorem linear_piece_integrableOn {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    IntegrableOn (fun u : ℝ => ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1))
      (Ioi (X : ℝ)) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hX
  have h1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s)) (Ioi (X : ℝ)) := by
    apply integrableOn_Ioi_cpow_of_lt _ hXpos
    simp only [Complex.neg_re]
    linarith
  have h2 : IntegrableOn (fun u : ℝ => (X : ℂ) * (u : ℂ) ^ (-s - 1)) (Ioi (X : ℝ)) := by
    apply Integrable.const_mul
    apply integrableOn_Ioi_cpow_of_lt _ hXpos
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  apply (h1.sub h2).congr_fun _ measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans hXpos hu
  have hne : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu0
  have hpow : (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
    rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
    field_simp
  show (u : ℂ) ^ (-s) - (X : ℂ) * (u : ℂ) ^ (-s - 1) =
      ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1)
  rw [← hpow]
  ring

/-- E1c split: the counted integral equals the linear integral minus the tail. -/
theorem count_integral_split {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    (∫ u in Ioi (X : ℝ), ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1)) =
      (∫ u in Ioi (X : ℝ), ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1)) -
        emTail s (X : ℝ) := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hX
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  rw [emTail, ← MeasureTheory.integral_sub (linear_piece_integrableOn hs hX)
    (emTailIntegrand_integrableOn hs0 hX1)]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans hXpos hu
  have hXfloor : X ≤ ⌊u⌋₊ := Nat.le_floor (le_of_lt hu)
  have hcast : ((⌊u⌋₊ - X : ℕ) : ℂ) = ((⌊u⌋₊ : ℕ) : ℂ) - (X : ℂ) := by
    push_cast [Nat.cast_sub hXfloor]
    ring
  show ((⌊u⌋₊ - X : ℕ) : ℂ) * (u : ℂ) ^ (-s - 1) =
      ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1) - emTailIntegrand s u
  rw [hcast, natCast_floor_eq_sub_fract hu0]
  unfold emTailIntegrand
  ring

/-- E1c evaluation: `s·∫_{Ioi X} (u−X)·u^{−s−1} du = X^{1−s}/(s−1)` for `Re s > 1`. -/
theorem linear_part_integral {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    s * ∫ u in Ioi (X : ℝ), ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1) =
      (X : ℂ) ^ (1 - s) / (s - 1) := by
  have hXpos : (0 : ℝ) < (X : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hX
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; simp at hs
  have ha1 : (-s : ℂ).re < -1 := by simp only [Complex.neg_re]; linarith
  have ha2 : (-s - 1 : ℂ).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith
  have hXne : ((X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hXpos
  have hsplit : (∫ u in Ioi (X : ℝ), ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1)) =
      (∫ u in Ioi (X : ℝ), (u : ℂ) ^ (-s)) -
        ∫ u in Ioi (X : ℝ), (X : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [← MeasureTheory.integral_sub (integrableOn_Ioi_cpow_of_lt ha1 hXpos)
      ((integrableOn_Ioi_cpow_of_lt ha2 hXpos).const_mul _)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans hXpos hu
    have hne : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu0
    have hpow : (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
      rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
      field_simp
    show ((u : ℂ) - (X : ℂ)) * (u : ℂ) ^ (-s - 1) =
        (u : ℂ) ^ (-s) - (X : ℂ) * (u : ℂ) ^ (-s - 1)
    rw [← hpow]
    ring
  rw [hsplit, MeasureTheory.integral_const_mul,
    integral_Ioi_cpow_of_lt ha1 hXpos, integral_Ioi_cpow_of_lt ha2 hXpos]
  have e1 : (-s : ℂ) + 1 = -(s - 1) := by ring
  have e2 : (-s - 1 : ℂ) + 1 = -s := by ring
  have hXpow : ((X : ℝ) : ℂ) ^ (-(s - 1) : ℂ) = ((X : ℝ) : ℂ) ^ (1 - s : ℂ) := by
    congr 1
    ring
  have hXpow2 : ((X : ℝ) : ℂ) * ((X : ℝ) : ℂ) ^ (-s : ℂ) =
      ((X : ℝ) : ℂ) ^ (1 - s : ℂ) := by
    rw [show (1 - s : ℂ) = 1 + -s from by ring, Complex.cpow_add _ _ hXne,
      Complex.cpow_one]
  rw [e1, e2, neg_div_neg_eq, neg_div_neg_eq, hXpow, ← hXpow2]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  push_cast at hXpow2 ⊢
  field_simp
  linear_combination hXpow2

/-- E1 assembled: the Euler–Maclaurin identity for `ζ` on `Re s > 1`. -/
theorem emIdentity_of_one_lt_re {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    riemannZeta s = (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) +
      (X : ℂ) ^ (1 - s) / (s - 1) - s * emTail s (X : ℝ) := by
  have h1 := zeta_sub_partial_eq_tsum_tail hs X
  have h2 := tsum_tail_eq_mul_integral_count hs X
  have h3 := count_integral_split hs hX
  have h4 := linear_part_integral hs hX
  have hchain : riemannZeta s - (∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-s)) =
      (X : ℂ) ^ (1 - s) / (s - 1) - s * emTail s (X : ℝ) := by
    rw [h1, h2, h3, mul_sub, h4]
  linear_combination hchain

end RH.Criteria.NymanBeurling.H14ZetaEM

