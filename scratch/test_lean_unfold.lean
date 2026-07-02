import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
  unfold cotangentSumVFormula
  -- At this point we have ∑ a ∈ Finset.Ico 1 3, ...
  have h1 : (3 : ℕ) = 2 + 1 := rfl
  rw [h1]
  rw [Finset.sum_Ico_succ_top (by decide)]
  -- Now we have ∑ a ∈ Finset.Ico 1 2, ...
  have h2 : (2 : ℕ) = 1 + 1 := rfl
  rw [h2]
  rw [Finset.sum_Ico_succ_top (by decide)]
  -- Now we have ∑ a ∈ Finset.Ico 1 1, ...
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  
  -- Now replace fracts
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / (3 : ℝ)) = 2 / 3 := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / (3 : ℝ)) = 1 / 3 := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  ring
