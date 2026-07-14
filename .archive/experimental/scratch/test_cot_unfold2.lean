import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

open RH.Criteria.NymanBeurling.VasyuninGram
open scoped Finset

noncomputable def cotTerm2 (a k : ℕ) : ℝ :=
  Real.cos (Real.pi * (a : ℝ) / (k : ℝ)) /
  Real.sin (Real.pi * (a : ℝ) / (k : ℝ))

lemma sum_Ico_1_3 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 3, f a = f 1 + f 2 := by
  have h1 : Finset.Ico 1 3 = {1, 2} := rfl
  rw [h1, Finset.sum_insert, Finset.sum_singleton]
  decide

theorem cotangentSumVFormula_2_3_unfold :
    cotangentSumVFormula 2 3 =
      (2/3 : ℝ) * cotTerm2 1 3
    + (1/3 : ℝ) * cotTerm2 2 3 := by
  unfold cotangentSumVFormula cotTerm2
  rw [sum_Ico_1_3]
  -- We just want to simplify the rational arithmetic and Int.fract, but leave Real.cos/sin alone.
  have hf1 : Int.fract (((1 * 2 : ℕ) : ℝ) / (3 : ℝ)) = 2/3 := by norm_num [Int.fract]
  have hf2 : Int.fract (((2 * 2 : ℕ) : ℝ) / (3 : ℝ)) = 1/3 := by norm_num [Int.fract]
  rw [hf1, hf2]
  ring

axiom cot_pi_1_3_bounds :
  (0.5773502691896257 : ℝ) ≤ cotTerm2 1 3 ∧
  cotTerm2 1 3 ≤ (0.5773502691896258 : ℝ)

axiom cot_pi_2_3_bounds :
  (-0.5773502691896258 : ℝ) ≤ cotTerm2 2 3 ∧
  cotTerm2 2 3 ≤ (-0.5773502691896257 : ℝ)

theorem cotangentSumVFormula_2_3_bounds_test :
    (0.19245008972987523 : ℝ) ≤ cotangentSumVFormula 2 3 ∧
    cotangentSumVFormula 2 3 ≤ (0.1924500897298753 : ℝ) := by
  rw [cotangentSumVFormula_2_3_unfold]
  have h1 := cot_pi_1_3_bounds
  have h2 := cot_pi_2_3_bounds
  constructor
  · nlinarith
  · nlinarith
