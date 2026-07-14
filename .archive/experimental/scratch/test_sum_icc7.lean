import RiemannHypothesis.Criteria.NymanBeurling.CutoffMobiusKernels

open Finset
open scoped BigOperators

theorem sum_fin_eq_sum_Icc_one
    (N : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin N, f (i.val + 1))
      =
    ∑ k ∈ Icc 1 N, f k := by
  have h1 : (∑ i : Fin N, f (i.val + 1)) = ∑ k ∈ range N, f (k + 1) := by
    exact Fin.sum_univ_eq_sum_range (fun i ↦ f (i + 1)) N
  have h2 : ∑ k ∈ range N, f (k + 1) = ∑ k ∈ Ico 1 (N + 1), f k := by
    have h_sub : N = N + 1 - 1 := by omega
    nth_rw 1 [h_sub]
    have eq_ico := (sum_Ico_eq_sum_range (fun i ↦ f i) 1 (N + 1)).symm
    have hc : (fun (k : ℕ) ↦ f (1 + k)) = (fun (k : ℕ) ↦ f (k + 1)) := by
      ext x
      rw [add_comm]
    rw [←hc]
    exact eq_ico
  have h3 : Ico 1 (N + 1) = Icc 1 N := by
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  rw [h1, h2, h3]

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

