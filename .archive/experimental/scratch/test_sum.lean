import Mathlib

open scoped BigOperators

def f : Fin 2 → ℚ
| ⟨0, _⟩ => 1
| ⟨1, _⟩ => 2

theorem test_sum : (∑ k : Fin 2, f k) = 3 := by
  norm_num
