import Mathlib.Data.Real.Basic

open scoped Finset

lemma sum_Ico_1_10 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 10, f a = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  have h1 : Finset.Ico 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := rfl
  rw [h1]
  simp only [Finset.sum_insert, Finset.sum_singleton, Nat.cast_one, Nat.cast_ofNat]
  -- sometimes simp needs to know the element isn't in the rest of the set
  -- wait, simp might fail to evaluate the non-membership
