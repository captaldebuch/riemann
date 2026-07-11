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

end RH.Criteria.NymanBeurling.H14ZetaFETransport
