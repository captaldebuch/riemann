import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Intervals

open Finset

theorem sum_fin_eq_sum_icc_1 (N : ℕ) (f : ℕ → ℝ) :
  (∑ i : Fin N, f (i.val + 1)) = ∑ k in Icc 1 N, f k := by
  have h1 : (∑ i : Fin N, f (i.val + 1)) = ∑ i in range N, f (i + 1) := by
    exact sum_range fun i ↦ f (i + 1)
  rw [h1]
  exact sum_Ico_eq_sum_range (fun i ↦ f i) 1 (N + 1)
