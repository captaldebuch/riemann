import Mathlib

def myM : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![2, 1],
    ![1, 2]]

def myL : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![1, 0],
    ![1/2, 1]]

def myD : Fin 2 → ℚ := ![2, 3/2]

theorem check_fac : ∀ i j, myM i j = (myL * Matrix.diagonal myD * myLᵀ) i j := by
  decide

theorem check_psd : ∀ i, 0 ≤ myD i := by
  decide
