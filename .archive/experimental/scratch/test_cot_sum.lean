import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

open RH.Criteria.NymanBeurling.VasyuninGram

axiom cot_pi_1_3_bounds :
  (0.5773502691896257 : ℝ) ≤ (Real.cos (Real.pi * 1 / 3) / Real.sin (Real.pi * 1 / 3)) ∧
  (Real.cos (Real.pi * 1 / 3) / Real.sin (Real.pi * 1 / 3)) ≤ (0.5773502691896258 : ℝ)

axiom cot_pi_2_3_bounds :
  (-0.5773502691896258 : ℝ) ≤ (Real.cos (Real.pi * 2 / 3) / Real.sin (Real.pi * 2 / 3)) ∧
  (Real.cos (Real.pi * 2 / 3) / Real.sin (Real.pi * 2 / 3)) ≤ (-0.5773502691896257 : ℝ)

theorem cotangentSumVFormula_2_3_bounds_test :
  (0.19245008972987523 : ℝ) ≤ cotangentSumVFormula 2 3 ∧
  cotangentSumVFormula 2 3 ≤ (0.1924500897298753 : ℝ) := by
  unfold cotangentSumVFormula
  have h_cot1 := cot_pi_1_3_bounds
  have h_cot2 := cot_pi_2_3_bounds
  -- Evaluate the sum and fracts
  norm_num [Finset.sum_Ico_succ_top, Int.fract]
  linarith
