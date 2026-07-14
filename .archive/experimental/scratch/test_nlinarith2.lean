import Mathlib

theorem test_prod_bounds (pi S : ℝ)
  (hpi_lo : 3.14 ≤ pi) (hpi_hi : pi ≤ 3.15)
  (hS_lo : 0.19 ≤ S) (hS_hi : S ≤ 0.20) :
  (0.59 : ℝ) ≤ pi * S ∧ pi * S ≤ (0.64 : ℝ) := by
  constructor
  · nlinarith
  · nlinarith
