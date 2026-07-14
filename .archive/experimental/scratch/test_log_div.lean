import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

theorem test_log_div (h k : ℕ) (h_pos : (0:ℝ) < h) (k_pos : (0:ℝ) < k) :
  Real.log ((h:ℝ) / (k:ℝ)) = Real.log (h:ℝ) - Real.log (k:ℝ) := by
  exact Real.log_div (ne_of_gt h_pos) (ne_of_gt k_pos)

theorem test_log_1_k (k : ℕ) (k_pos : (0:ℝ) < k) :
  Real.log (1 / (k:ℝ)) = - Real.log (k:ℝ) := by
  rw [one_div, Real.log_inv]
