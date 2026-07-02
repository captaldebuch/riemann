import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

def cot_pi_10_21_lower : ℚ := 5399970157843809 / 72057594037927936

example (x : ℝ) (h : (5399970157843809 / 72057594037927936 : ℝ) ≤ x) : ((cot_pi_10_21_lower : ℚ) : ℝ) ≤ x := by
  norm_num [cot_pi_10_21_lower]
  linarith [h]

