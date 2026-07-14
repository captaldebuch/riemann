import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

example (x : ℝ) (v1 v2 : ℚ) (h : x ≤ (v1 : ℝ)) (h2 : ((v2 : ℚ) : ℝ) ≤ -(v1 : ℝ)) : (v2 : ℝ) ≤ -x := by
  have h1 : -(v1 : ℝ) ≤ -x := neg_le_neg h
  exact le_trans h2 h1

