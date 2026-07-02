import Mathlib

open scoped BigOperators

def D_val : Fin 2 → ℚ := ![1, 2]
def L_val : Fin 2 → Fin 2 → ℚ := ![![1, 0], ![(1/2), 1]]

theorem test_sum (i j : Fin 2) : (∑ k : Fin 2, L_val i k * D_val k * L_val j k) = 0 := by
  fin_cases i <;> fin_cases j
  · simp [Fin.sum_univ_succ, Fin.sum_univ_zero, D_val, L_val]; norm_num
  · simp [Fin.sum_univ_succ, Fin.sum_univ_zero, D_val, L_val]; norm_num
  · simp [Fin.sum_univ_succ, Fin.sum_univ_zero, D_val, L_val]; norm_num
  · simp [Fin.sum_univ_succ, Fin.sum_univ_zero, D_val, L_val]; norm_num
