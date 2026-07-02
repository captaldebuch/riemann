import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

namespace RH.Criteria.NymanBeurling.VasyuninGram

open RH.Criteria.NymanBeurling.BaezDuarte

-- ---------------------------------------------------------------------------
-- 1. Symmetric properties
-- ---------------------------------------------------------------------------

/-- The integral of fractional parts over an interval [1/(m+1), 1/m] -/
noncomputable def fractionalPartIntervalIntegral (h k m : ℕ) : ℝ :=
  ∫ x in Set.Ioc (1 / ((m + 1 : ℝ))) (1 / ((m : ℝ))),
    (Int.fract (1 / ((h : ℝ) * x))) * (Int.fract (1 / ((k : ℝ) * x)))
-- ---------------------------------------------------------------------------
-- 5. Main Theorem Replacement
-- ---------------------------------------------------------------------------

structure VasyuninBridgeLocalDebts where
  vasyuninBEntry_symm :
    ∀ h k : ℕ, vasyuninBEntry h k = vasyuninBEntry k h
  vasyuninBEntry_diagonal :
    ∀ h : ℕ, baezDuarteGramEntry h h = vasyuninBEntry h h
  baezDuarteGramEntry_eq_tsum_intervals :
    ∀ h k : ℕ, baezDuarteGramEntry h k = ∑' m : ℕ, fractionalPartIntervalIntegral h k m
  interval_sum_eq_cotangent_formula :
    ∀ h k : ℕ, h ≠ k → (∑' m : ℕ, fractionalPartIntervalIntegral h k m) = vasyuninBEntry h k

theorem vasyuninBEntry_correct_of_local_debts
    (H : VasyuninBridgeLocalDebts) (h k : ℕ) :
    baezDuarteGramEntry h k = vasyuninBEntry h k := by
  by_cases h_eq : h = k
  · rw [h_eq]
    exact H.vasyuninBEntry_diagonal k
  · rw [H.baezDuarteGramEntry_eq_tsum_intervals h k]
    exact H.interval_sum_eq_cotangent_formula h k h_eq

theorem vasyuninBEntry_correct_axiom (h k : ℕ) :
    baezDuarteGramEntry h k = vasyuninBEntry h k := by
  sorry

end RH.Criteria.NymanBeurling.VasyuninGram
