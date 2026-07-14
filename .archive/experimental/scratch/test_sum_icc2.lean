import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Interval

open Finset

theorem sum_fin_eq_sum_range_succ
    (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, f (i.val + 1))
      =
    ∑ k in range N, f (k + 1) := by
  exact sum_range fun i ↦ f (i + 1)

theorem sum_range_succ_eq_sum_Ico_one
    (N : ℕ) (f : ℕ → ℝ) :
    (∑ k in range N, f (k + 1))
      =
    ∑ k in Ico 1 (N + 1), f k := by
  exact sum_Ico_eq_sum_range (fun i ↦ f i) 1 (N + 1)

theorem sum_Ico_one_eq_sum_Icc_one
    (N : ℕ) (f : ℕ → ℝ) :
    (∑ k in Ico 1 (N + 1), f k)
      =
    ∑ k in Icc 1 N, f k := by
  have h : Ico 1 (N + 1) = Icc 1 N := Nat.Ico_succ_right
  rw [h]

theorem sum_fin_eq_sum_Icc_one
    (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, f (i.val + 1))
      =
    ∑ k in Icc 1 N, f k := by
  rw [sum_fin_eq_sum_range_succ, sum_range_succ_eq_sum_Ico_one, sum_Ico_one_eq_sum_Icc_one]

