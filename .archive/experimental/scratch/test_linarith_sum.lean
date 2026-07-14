import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

axiom c1 : ℝ
axiom c2 : ℝ
axiom c1_bound : (0.1 : ℝ) ≤ c1 ∧ c1 ≤ 0.2
axiom c2_bound : (0.3 : ℝ) ≤ c2 ∧ c2 ≤ 0.4

theorem test : (0.13 : ℝ) ≤ (1/3 : ℝ) * c1 + (1/3 : ℝ) * c2 ∧ (1/3 : ℝ) * c1 + (1/3 : ℝ) * c2 ≤ (0.21 : ℝ) := by
  have b1 := c1_bound
  have b2 := c2_bound
  constructor
  · linarith
  · linarith
