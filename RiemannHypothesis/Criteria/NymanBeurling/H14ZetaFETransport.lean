import RiemannHypothesis.Criteria.NymanBeurling.H14ZetaEM

/-!
# A2: transporting vertical growth to the left strip

Slice A2a: the elementary series bound `‖ζ(s)‖ ≤ 9` for `Re s ≥ 9/8`,
via termwise norms and the sum–integral comparison.
-/

namespace RH.Criteria.NymanBeurling.H14ZetaFETransport

open Complex MeasureTheory Set Filter Topology intervalIntegral

/-- Sum–integral comparison for the `9/8`-series: partial sums stay below 9. -/
theorem sum_range_rpow_nine_eighths_le (N : ℕ) :
    (∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ))) ≤ 9 := by
  induction N with
  | zero => simp
  | succ M _ =>
    clear ‹_›
    have hanti : AntitoneOn (fun u : ℝ => u ^ (-(9 / 8 : ℝ)))
        (Icc (1 : ℝ) (1 + M)) := by
      intro u hu v hv huv
      have h1 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu.1
      have h2 : (0 : ℝ) < v := lt_of_lt_of_le h1 huv
      simp only
      rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, ← one_div, ← one_div]
      apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos h1 _)
      exact Real.rpow_le_rpow h1.le huv (by norm_num)
    have hcomp := hanti.sum_le_integral (x₀ := (1 : ℝ)) (a := M)
    have hint : (∫ x in (1 : ℝ)..(1 + M : ℝ), x ^ (-(9 / 8 : ℝ))) ≤ 8 := by
      have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + M : ℝ) := by
        rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg M))]
        intro h
        exact absurd h.1 (by norm_num)
      rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
      have hpow : (0 : ℝ) < (1 + (M : ℝ)) ^ (-(9 / 8 : ℝ) + 1) := by
        apply Real.rpow_pos_of_pos
        positivity
      rw [Real.one_rpow]
      rw [show (-(9 / 8 : ℝ) + 1) = -(1 / 8 : ℝ) from by norm_num] at hpow ⊢
      have : ((1 + (M : ℝ)) ^ (-(1 / 8 : ℝ)) - 1) / (-(1 / 8 : ℝ)) =
          8 * (1 - (1 + (M : ℝ)) ^ (-(1 / 8 : ℝ))) := by ring
      rw [this]
      nlinarith [hpow]
    rw [Finset.sum_range_succ']
    have hzero : ((0 + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) = 1 := by
      norm_num
    rw [hzero]
    have hmatch : (∑ i ∈ Finset.range M, ((i + 1 + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ))) =
        ∑ i ∈ Finset.range M, (fun u : ℝ => u ^ (-(9 / 8 : ℝ))) ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    rw [hmatch]
    linarith [le_trans hcomp hint]

/-- A2a: the elementary zeta bound on `Re s ≥ 9/8`. -/
theorem norm_riemannZeta_le_of_re_ge {s : ℂ} (hs : (9 / 8 : ℝ) ≤ s.re) :
    ‖riemannZeta s‖ ≤ 9 := by
  have hs1 : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1]
  have hnorm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) := by
    intro n
    have hcast : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h1le : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)
    rw [norm_div, norm_one, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
      one_div, ← Real.rpow_neg hpos.le]
    apply Real.rpow_le_rpow_of_exponent_le h1le
    linarith
  have hsummaj : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) := by
    have h1 := Real.summable_nat_rpow.mpr (show (-(9/8) : ℝ) < -1 by norm_num)
    have h2 := h1.comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) from fun a b hab => by
        simpa using hab)
    apply h2.congr
    intro n
    simp only [Function.comp_apply]
  have hnormsum : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ s‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hsummaj
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-(9 / 8 : ℝ)) :=
        hnormsum.tsum_le_tsum hnorm hsummaj
    _ ≤ 9 := Real.tsum_le_of_sum_range_le (fun n => by positivity)
        sum_range_rpow_nine_eighths_le

/-! ## A2b: sqrt- and log-strength exports from the A1 components

Numerics gates (recorded): `max |ζ|/√(|t|+2) = 0.72` on `σ∈[1/2,2]` (claim 6),
`max |ζ|/(1+log(|t|+2)) = 0.60` on `σ∈[1,2]` (claim 4). -/

open RH.Criteria.NymanBeurling.H14ZetaEM

/-- Harmonic partial sums: `Σ_{n<N} 1/(n+1) ≤ 1 + log (N)` for `N ≥ 1`,
in the inclusive form `≤ 1 + log (N + 1)` valid for all `N`. -/
theorem sum_range_inv_le (N : ℕ) :
    (∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ))⁻¹) ≤ 1 + Real.log (N + 1) := by
  induction N with
  | zero => simp
  | succ M _ =>
    clear ‹_›
    have hanti : AntitoneOn (fun u : ℝ => u⁻¹) (Icc (1 : ℝ) (1 + M)) := by
      intro u hu v hv huv
      have h1 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu.1
      simp only
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le h1 huv
    have hcomp := hanti.sum_le_integral (x₀ := (1 : ℝ)) (a := M)
    have hint : (∫ x in (1 : ℝ)..(1 + M : ℝ), x⁻¹) = Real.log (1 + M) := by
      rw [integral_inv (by
        rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg M))]
        intro h
        exact absurd h.1 (by norm_num))]
      rw [div_eq_mul_inv, mul_comm, ← div_eq_inv_mul]
      norm_num
    rw [Finset.sum_range_succ']
    have hzero : (((0 + 1 : ℕ) : ℝ))⁻¹ = 1 := by norm_num
    rw [hzero]
    have hmatch : (∑ i ∈ Finset.range M, (((i + 1 + 1 : ℕ) : ℝ))⁻¹) =
        ∑ i ∈ Finset.range M, (fun u : ℝ => u⁻¹) ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    have hlogmono : Real.log (1 + M) ≤ Real.log (M + 1 + 1) := by
      apply Real.log_le_log (by positivity)
      push_cast
      linarith
    rw [hmatch]
    push_cast
    have := le_trans hcomp (le_of_eq hint)
    push_cast at this hlogmono
    linarith

/-- Floor cutoff comparisons used repeatedly below. -/
theorem floorX_le {t : ℝ} : ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) ≤ |t| + 2 := by
  push_cast
  linarith [Nat.floor_le (abs_nonneg t)]

theorem le_floorX {t : ℝ} : |t| + 1 ≤ ((⌊|t|⌋₊ + 2 : ℕ) : ℝ) := by
  push_cast
  linarith [Nat.lt_floor_add_one |t|]

/-- A2b sqrt-strength: `‖ζ(σ+it)‖ ≤ 6√(|t|+2)` on `σ ∈ [1/2,2]`, `|t| ≥ 1`. -/
theorem norm_riemannZeta_le_sqrt {σ t : ℝ} (hσl : (1 / 2 : ℝ) ≤ σ)
    (hσh : σ ≤ 2) (ht : (1 : ℝ) ≤ |t|) :
    ‖riemannZeta (σ + Complex.I * t : ℂ)‖ ≤ 6 * Real.sqrt (|t| + 2) := by
  set X : ℕ := ⌊|t|⌋₊ + 2 with hXdef
  have htabs : (0 : ℝ) < |t| := lt_of_lt_of_le one_pos ht
  have hX1 : (1 : ℝ) ≤ ((X : ℕ) : ℝ) := le_trans (by linarith) le_floorX
  have hXpos : (0 : ℝ) < ((X : ℕ) : ℝ) := lt_of_lt_of_le one_pos hX1
  have hsq2 : (0 : ℝ) < Real.sqrt (|t| + 2) := Real.sqrt_pos.mpr (by linarith)
  have hdec := zetaRightHalfEulerMaclaurinComponents.decomposition
    (σ := σ) (t := t) hσl hσh (by simpa using ht)
  -- unfold the instance fields
  simp only [zetaRightHalfEulerMaclaurinComponents] at hdec
  rw [hdec]
  have hsre : (σ + Complex.I * t : ℂ).re = σ := re_sigma_add_I_mul σ t
  -- partial
  have hpartial : ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ ≤
      2 * Real.sqrt (|t| + 2) := by
    calc ‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖
        ≤ 2 * Real.sqrt ((X : ℕ) : ℝ) := partialSum_norm_le hσl t X
      _ ≤ 2 * Real.sqrt (|t| + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.sqrt_le_sqrt floorX_le
  -- pole
  have hpole : ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) /
      ((σ + Complex.I * t : ℂ) - 1)‖ ≤ Real.sqrt (|t| + 2) := by
    have hXposn : (0 : ℕ) < X := by omega
    have hnum : ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ))‖ =
        ((X : ℕ) : ℝ) ^ (1 - σ) := by
      rw [Complex.norm_natCast_cpow_of_pos hXposn]
      congr 1
      rw [Complex.sub_re, Complex.one_re, hsre]
    have hden : (1 : ℝ) ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := by
      calc (1 : ℝ) ≤ |t| := ht
        _ = |((σ + Complex.I * t : ℂ) - 1).im| := by
            rw [Complex.sub_im, Complex.one_im, im_sigma_add_I_mul]
            simp
        _ ≤ ‖(σ + Complex.I * t : ℂ) - 1‖ := Complex.abs_im_le_norm _
    rw [norm_div, hnum]
    calc ((X : ℕ) : ℝ) ^ (1 - σ) / ‖(σ + Complex.I * t : ℂ) - 1‖
        ≤ ((X : ℕ) : ℝ) ^ (1 - σ) / 1 := by
          apply div_le_div_of_nonneg_left _ one_pos hden
          positivity
      _ = ((X : ℕ) : ℝ) ^ (1 - σ) := div_one _
      _ ≤ ((X : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = Real.sqrt ((X : ℕ) : ℝ) := (Real.sqrt_eq_rpow _).symm
      _ ≤ Real.sqrt (|t| + 2) := Real.sqrt_le_sqrt floorX_le
  -- tail
  have htail : ‖-((σ + Complex.I * t : ℂ) *
      emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ ≤ 3 * Real.sqrt (|t| + 2) := by
    have htl : ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖ ≤
        ((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * 2 := by
      calc ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖
          ≤ ((X : ℕ) : ℝ) ^ (-(σ + Complex.I * t : ℂ).re) /
              (σ + Complex.I * t : ℂ).re :=
            emTail_norm_le (by rw [hsre]; exact hσl) hX1
        _ ≤ ((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * 2 := by
            rw [hsre]
            rw [div_eq_mul_inv]
            apply mul_le_mul
            · exact Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
            · rw [← one_div]
              rw [div_le_iff₀ (by linarith)]
              linarith
            · positivity
            · positivity
    have hs_norm : ‖(σ + Complex.I * t : ℂ)‖ ≤ |t| + 2 := by
      calc ‖(σ + Complex.I * t : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ :=
            norm_add_le _ _
        _ = |σ| + |t| := by
            rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real]
            simp [Real.norm_eq_abs]
        _ ≤ 2 + |t| := by
            have : |σ| ≤ 2 := abs_le.mpr ⟨by linarith, hσh⟩
            linarith
        _ = |t| + 2 := by ring
    have hXlow : ((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤
        Real.sqrt 2 / Real.sqrt (|t| + 2) := by
      have h2X : |t| + 2 ≤ 2 * ((X : ℕ) : ℝ) := by
        have := le_floorX (t := t)
        linarith
      rw [Real.rpow_neg hXpos.le, ← Real.sqrt_eq_rpow, ← one_div,
        div_le_div_iff₀ (Real.sqrt_pos.mpr hXpos) hsq2]
      rw [one_mul, ← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      linarith
    calc ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖
        = ‖(σ + Complex.I * t : ℂ)‖ * ‖emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ)‖ := by
          rw [norm_neg, norm_mul]
      _ ≤ (|t| + 2) * (((X : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * 2) := by
          apply mul_le_mul hs_norm htl (norm_nonneg _) (by positivity)
      _ ≤ (|t| + 2) * (Real.sqrt 2 / Real.sqrt (|t| + 2) * 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hXlow (by norm_num)
      _ = 2 * Real.sqrt 2 * ((|t| + 2) / Real.sqrt (|t| + 2)) := by ring
      _ = 2 * Real.sqrt 2 * Real.sqrt (|t| + 2) := by
          rw [Real.div_sqrt]
      _ ≤ 3 * Real.sqrt (|t| + 2) := by
          apply mul_le_mul_of_nonneg_right _ hsq2.le
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),
            Real.sqrt_nonneg (2 : ℝ)]
  calc ‖(∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))) +
        ((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1) +
        -((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖
      ≤ ‖(∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))) +
          ((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1)‖ +
        ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ :=
        norm_add_le _ _
    _ ≤ (‖∑ n ∈ Finset.Icc 1 X, (n : ℂ) ^ (-(σ + Complex.I * t : ℂ))‖ +
        ‖((X : ℕ) : ℂ) ^ (1 - (σ + Complex.I * t : ℂ)) / ((σ + Complex.I * t : ℂ) - 1)‖) +
        ‖-((σ + Complex.I * t : ℂ) * emTail (σ + Complex.I * t : ℂ) ((X : ℕ) : ℝ))‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ (2 * Real.sqrt (|t| + 2) + Real.sqrt (|t| + 2)) + 3 * Real.sqrt (|t| + 2) := by
        gcongr
    _ = 6 * Real.sqrt (|t| + 2) := by ring

end RH.Criteria.NymanBeurling.H14ZetaFETransport
