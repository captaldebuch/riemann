import Mathlib

def M_fn (i j : Fin 2) : ℚ :=
  if i.val == 0 ∧ j.val == 0 then 1
  else if i.val == 0 ∧ j.val == 1 then 2
  else if i.val == 1 ∧ j.val == 0 then 3
  else if i.val == 1 ∧ j.val == 1 then 4
  else 0

def M : Matrix (Fin 2) (Fin 2) ℚ := M_fn

theorem test1 : 0 ≤ M_fn 0 0 := by
  simp [M_fn]
  norm_num

theorem test2 (i j : Fin 2) : (M * M) i j = (M * M) i j := by
  fin_cases i <;> fin_cases j
  · simp [M, M_fn, Matrix.mul_apply, Finset.sum_range]
    norm_num
  · rfl
  · rfl
  · rfl
