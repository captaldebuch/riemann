import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

open RH.Criteria.NymanBeurling.VasyuninGram
open scoped Finset

noncomputable def cotTerm (a k : ℕ) : ℝ :=
  Real.cos (Real.pi * (a : ℝ) / (k : ℝ)) /
  Real.sin (Real.pi * (a : ℝ) / (k : ℝ))

lemma sum_Ico_1_3 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 3, f a = f 1 + f 2 := by
  have h1 : Finset.Ico 1 3 = {1, 2} := rfl
  rw [h1, Finset.sum_insert, Finset.sum_singleton]
  decide

theorem cotangentSumVFormula_2_3_unfold :
    cotangentSumVFormula 2 3 =
      (2/3 : ℝ) * cotTerm 1 3
    + (1/3 : ℝ) * cotTerm 2 3 := by
  unfold cotangentSumVFormula cotTerm
  rw [sum_Ico_1_3]
  norm_num [Int.fract]

axiom cot_pi_1_3_bounds :
  (0.5773502691896257 : ℝ) ≤ cotTerm 1 3 ∧
  cotTerm 1 3 ≤ (0.5773502691896258 : ℝ)

axiom cot_pi_2_3_bounds :
  (-0.5773502691896258 : ℝ) ≤ cotTerm 2 3 ∧
  cotTerm 2 3 ≤ (-0.5773502691896257 : ℝ)

theorem cotangentSumVFormula_2_3_bounds_test :
    (0.19245008972987523 : ℝ) ≤ cotangentSumVFormula 2 3 ∧
    cotangentSumVFormula 2 3 ≤ (0.1924500897298753 : ℝ) := by
  rw [cotangentSumVFormula_2_3_unfold]
  have h1 := cot_pi_1_3_bounds
  have h2 := cot_pi_2_3_bounds
  constructor
  · linarith
  · linarith
