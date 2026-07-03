import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Criteria.NymanBeurling.G11Formula

namespace RH.Criteria.NymanBeurling.VasyuninGram

theorem vasyuninBEntry_diagonal_scaling (k : ℕ) :
    vasyuninBEntry k k = (1 / (k : ℝ)) * vasyuninBEntry 1 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · unfold vasyuninBEntry vasyuninBEntryFormula cotangentSumVFormula
    simp
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hkR_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk_pos
    unfold vasyuninBEntry vasyuninBEntryFormula cotangentSumVFormula
    have h_vanish : ((k : ℝ) - (k : ℝ)) = 0 := sub_self _
    have h_sum : ∑ a ∈ Finset.Ico 1 k, Int.fract (((a * k : ℕ) : ℝ) / (k : ℝ)) * cotangentTermV a k = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have : (((a * k : ℕ) : ℝ) / (k : ℝ)) = a := by
        push_cast
        exact mul_div_cancel_right₀ _ (ne_of_gt hkR_pos)
      rw [this, Int.fract_natCast, zero_mul]
    simp only [h_vanish, zero_div, zero_mul, sub_zero, h_sum, add_zero, mul_zero]
    have h_one_one : vasyuninBEntry 1 1 = Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
      rw [vasyuninBEntry_eq_formula, vasyuninBEntryFormula_one_one]
    rw [h_one_one]
    ring

end RH.Criteria.NymanBeurling.VasyuninGram
