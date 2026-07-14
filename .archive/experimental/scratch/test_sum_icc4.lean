import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels

open Finset
open scoped BigOperators

theorem sum_fin_eq_sum_Icc_one
    (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, f (i.val + 1))
      =
    ∑ k ∈ Icc 1 N, f k := by
  have h1 : ∑ i : Fin N, f (i.val + 1) = ∑ k ∈ range N, f (k + 1) := by
    exact Fin.sum_univ_eq_sum_range (fun i ↦ f (i + 1))
  have h2 : ∑ k ∈ Icc 1 N, f k = ∑ k ∈ range (N + 1 - 1), f (1 + k) := by
    exact Finset.sum_Icc_eq_sum_range (fun i ↦ f i) 1 N
  rw [h1, h2]
  have h3 : N + 1 - 1 = N := by omega
  rw [h3]
  apply Finset.sum_congr rfl
  intro x _
  rw [add_comm]

theorem sum_fin_fin_eq_sum_Icc_Icc
    (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, f (i.val + 1) (j.val + 1))
      =
    ∑ h ∈ Icc 1 N,
      ∑ k ∈ Icc 1 N,
        f h k := by
  rw [sum_fin_eq_sum_Icc_one]
  apply Finset.sum_congr rfl
  intro h _
  rw [sum_fin_eq_sum_Icc_one]

