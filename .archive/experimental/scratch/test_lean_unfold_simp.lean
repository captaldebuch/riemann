import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

open RH.Criteria.NymanBeurling.VasyuninGram
open scoped Finset

noncomputable def cotTerm2 (a k : ℕ) : ℝ :=
  Real.cos (Real.pi * (a : ℝ) / (k : ℝ)) /
  Real.sin (Real.pi * (a : ℝ) / (k : ℝ))

theorem cotangentSumVFormula_2_3_unfold :
    cotangentSumVFormula 2 3 =
      (2/3 : ℝ) * cotTerm2 1 3
    + (1/3 : ℝ) * cotTerm2 2 3 := by
  unfold cotangentSumVFormula cotTerm2
  have h_set : Finset.Ico 1 3 = {1, 2} := rfl
  rw [h_set]
  simp only [Finset.sum_insert, Finset.sum_singleton, Nat.cast_one, Nat.cast_ofNat]
  
  -- The sum is expanded! Now just fractions:
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / (3 : ℝ)) = 2 / 3 := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / (3 : ℝ)) = 1 / 3 := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  ring
