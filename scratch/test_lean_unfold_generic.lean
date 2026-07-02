import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped Finset

lemma sum_Ico_1_4 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 4, f a = f 1 + f 2 + f 3 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  ring

lemma sum_Ico_1_3 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 3, f a = f 1 + f 2 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  ring
