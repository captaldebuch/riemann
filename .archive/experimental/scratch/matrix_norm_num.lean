import Mathlib

def myM : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![2, 1],
    ![1, 2]]

def myL : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![1, 0],
    ![1/2, 1]]

def myD : Fin 2 → ℚ := ![2, 3/2]

theorem check_fac : myM = myL * Matrix.diagonal myD * Matrix.transpose myL := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem check_psd : ∀ i : Fin 2, 0 ≤ myD i := by
  intro i
  fin_cases i <;> norm_num
