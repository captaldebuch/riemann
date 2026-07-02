import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula

open RH.Criteria.NymanBeurling.VasyuninGram
open scoped Finset

lemma sum_Ico_1_3 (f : ℕ → ℝ) : ∑ a ∈ Finset.Ico 1 3, f a = f 1 + f 2 := by
  rw [Finset.sum_Ico_succ_top (by decide)]
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]

theorem cotangentSumVFormula_2_3_unfold :
    cotangentSumVFormula 2 3 =
      (2/3 : ℝ) * cotangentTermV 1 3    + 
      (1/3 : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = (2 : ℝ) / 3 := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = (1 : ℝ) / 3 := by norm_num [Int.fract]
  rw [hf_1, hf_2]
  ring
