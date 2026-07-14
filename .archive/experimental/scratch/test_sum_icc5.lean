import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels

open Finset
open scoped BigOperators

theorem sum_fin_eq_sum_Icc_one
    (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, f (i.val + 1))
      =
    ∑ k ∈ Icc 1 N, f k := by
  have h1 : (∑ i : Fin N, f (i.val + 1)) = ∑ k ∈ range N, f (k + 1) := by
    rw [Fin.sum_univ_eq_sum_range]
  have h2 : ∑ k ∈ range N, f (k + 1) = ∑ k ∈ Ico 1 (N + 1), f k := by
    have h_sub : N = N + 1 - 1 := by omega
    nth_rw 1 [h_sub]
    have eq_ico := (sum_Ico_eq_sum_range (fun i ↦ f i) 1 (N + 1)).symm
    have hc : (fun (k : ℕ) ↦ f (1 + k)) = (fun (k : ℕ) ↦ f (k + 1)) := by
      ext x
      rw [add_comm]
    rw [←hc]
    exact eq_ico
  have h3 : ∑ k ∈ Ico 1 (N + 1), f k = ∑ k ∈ Icc 1 N, f k := by
    rw [Nat.Ico_succ_right]
  rw [h1, h2, h3]

