import Mathlib

open Matrix

def M_reg : Matrix (Fin 2) (Fin 2) ℚ := ![![1, 2], ![3, 4]]
def D_val : Fin 2 → ℚ := ![5, 6]

theorem test1 : 0 ≤ D_val 0 := by
  simp [D_val]
  -- How to reduce ![5, 6] 0 ?
  simp [Matrix.vecCons]
  norm_num

theorem test2 (i j : Fin 2) : M_reg i j = M_reg i j := by
  fin_cases i <;> fin_cases j
  · simp [M_reg, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Matrix.empty]
    norm_num
  · rfl
  · rfl
  · rfl

theorem test3 (i j : Fin 2) : (M_reg * M_reg) i j = (M_reg * M_reg) i j := by
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, M_reg, Matrix.vecCons, Matrix.vecHead, Matrix.vecTail]
    norm_num
  · rfl
  · rfl
  · rfl
