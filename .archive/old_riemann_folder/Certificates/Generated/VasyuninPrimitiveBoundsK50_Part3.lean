import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninExplicitFormula
import RiemannHypothesis.Certificates.Generated.ChiRhoBoundsN50
import RiemannHypothesis.Certificates.Generated.TranscendentalBoundsGenerated
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsCore
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals

namespace RH.Certificates.Generated
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated.ChiRhoBoundsN50
open scoped Finset

theorem cotangentSumVFormula_11_42_unfold :
    cotangentSumVFormula 11 42 =
      ((11/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_11_42_lower : ℚ := -1480784242831418958677 / 219902325555200000000
def cotangentSumVFormula_11_42_upper : ℚ := -1480784238433216197573 / 219902325555200000000
theorem cotangentSumVFormula_11_42_bounds :
  ((cotangentSumVFormula_11_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 42 ∧
  cotangentSumVFormula 11 42 ≤ ((cotangentSumVFormula_11_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_11_42_lower, cotangentSumVFormula_11_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_11_unfold :
    cotangentSumVFormula 42 11 =
      ((9/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_42_11_lower : ℚ := 962131392748326535771 / 439804651110400000000
def cotangentSumVFormula_42_11_upper : ℚ := 962131401544432839229 / 439804651110400000000
theorem cotangentSumVFormula_42_11_bounds :
  ((cotangentSumVFormula_42_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 11 ∧
  cotangentSumVFormula 42 11 ≤ ((cotangentSumVFormula_42_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_11_unfold]
  have b_cot_1 := cot_pi_1_11_bounds
  simp only [cot_pi_1_11_lower, cot_pi_1_11_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_11_bounds
  simp only [cot_pi_2_11_lower, cot_pi_2_11_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_11_bounds
  simp only [cot_pi_3_11_lower, cot_pi_3_11_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_11_bounds
  simp only [cot_pi_4_11_lower, cot_pi_4_11_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_11_bounds
  simp only [cot_pi_5_11_lower, cot_pi_5_11_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_11_bounds
  simp only [cot_pi_6_11_lower, cot_pi_6_11_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_11_bounds
  simp only [cot_pi_7_11_lower, cot_pi_7_11_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_11_bounds
  simp only [cot_pi_8_11_lower, cot_pi_8_11_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_11_bounds
  simp only [cot_pi_9_11_lower, cot_pi_9_11_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_11_bounds
  simp only [cot_pi_10_11_lower, cot_pi_10_11_upper] at b_cot_10
  rw [cotangentSumVFormula_42_11_lower, cotangentSumVFormula_42_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1142_formula_bound :
  (((96416545610911892877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 42) ∧
  (vasyuninBEntryFormula 11 42 ≤ ((96421049210545357123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_11_42_bounds
  have b_Vkh := cotangentSumVFormula_42_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_11_42_lower, cotangentSumVFormula_11_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_11_lower, cotangentSumVFormula_42_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_42_unfold :
    cotangentSumVFormula 13 42 =
      ((13/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 13 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_13_42_lower : ℚ := -2341522233659942685041 / 1759218604441600000000
def cotangentSumVFormula_13_42_upper : ℚ := -2341522198474319814959 / 1759218604441600000000
theorem cotangentSumVFormula_13_42_bounds :
  ((cotangentSumVFormula_13_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 42 ∧
  cotangentSumVFormula 13 42 ≤ ((cotangentSumVFormula_13_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_13_42_lower, cotangentSumVFormula_13_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_13_unfold :
    cotangentSumVFormula 42 13 =
      ((3/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_42_13_lower : ℚ := -705256799656117995479 / 439804651110400000000
def cotangentSumVFormula_42_13_upper : ℚ := -352628395430002135073 / 219902325555200000000
theorem cotangentSumVFormula_42_13_bounds :
  ((cotangentSumVFormula_42_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 13 ∧
  cotangentSumVFormula 42 13 ≤ ((cotangentSumVFormula_42_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_13_unfold]
  have b_cot_1 := cot_pi_1_13_bounds
  simp only [cot_pi_1_13_lower, cot_pi_1_13_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_13_bounds
  simp only [cot_pi_2_13_lower, cot_pi_2_13_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_13_bounds
  simp only [cot_pi_3_13_lower, cot_pi_3_13_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_13_bounds
  simp only [cot_pi_4_13_lower, cot_pi_4_13_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_13_bounds
  simp only [cot_pi_5_13_lower, cot_pi_5_13_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_13_bounds
  simp only [cot_pi_6_13_lower, cot_pi_6_13_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_13_bounds
  simp only [cot_pi_7_13_lower, cot_pi_7_13_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_13_bounds
  simp only [cot_pi_8_13_lower, cot_pi_8_13_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_13_bounds
  simp only [cot_pi_9_13_lower, cot_pi_9_13_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_13_bounds
  simp only [cot_pi_10_13_lower, cot_pi_10_13_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_13_bounds
  simp only [cot_pi_11_13_lower, cot_pi_11_13_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_13_bounds
  simp only [cot_pi_12_13_lower, cot_pi_12_13_upper] at b_cot_12
  rw [cotangentSumVFormula_42_13_lower, cotangentSumVFormula_42_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1342_formula_bound :
  (((22964244103505875563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 42) ∧
  (vasyuninBEntryFormula 13 42 ≤ ((45930740006828076999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_13_42_bounds
  have b_Vkh := cotangentSumVFormula_42_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_13_42_lower, cotangentSumVFormula_13_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_13_lower, cotangentSumVFormula_42_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_42_unfold :
    cotangentSumVFormula 17 42 =
      ((17/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 17 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_17_42_lower : ℚ := -2699063290194473881583 / 879609302220800000000
def cotangentSumVFormula_17_42_upper : ℚ := -2699063272601694868417 / 879609302220800000000
theorem cotangentSumVFormula_17_42_bounds :
  ((cotangentSumVFormula_17_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 42 ∧
  cotangentSumVFormula 17 42 ≤ ((cotangentSumVFormula_17_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_17_42_lower, cotangentSumVFormula_17_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_17_unfold :
    cotangentSumVFormula 42 17 =
      ((8/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_42_17_lower : ℚ := 1120956386264885129521 / 439804651110400000000
def cotangentSumVFormula_42_17_upper : ℚ := 280239098765252643401 / 109951162777600000000
theorem cotangentSumVFormula_42_17_bounds :
  ((cotangentSumVFormula_42_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 17 ∧
  cotangentSumVFormula 42 17 ≤ ((cotangentSumVFormula_42_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_17_unfold]
  have b_cot_1 := cot_pi_1_17_bounds
  simp only [cot_pi_1_17_lower, cot_pi_1_17_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_17_bounds
  simp only [cot_pi_2_17_lower, cot_pi_2_17_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_17_bounds
  simp only [cot_pi_3_17_lower, cot_pi_3_17_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_17_bounds
  simp only [cot_pi_4_17_lower, cot_pi_4_17_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_17_bounds
  simp only [cot_pi_5_17_lower, cot_pi_5_17_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_17_bounds
  simp only [cot_pi_6_17_lower, cot_pi_6_17_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_17_bounds
  simp only [cot_pi_7_17_lower, cot_pi_7_17_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_17_bounds
  simp only [cot_pi_8_17_lower, cot_pi_8_17_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_17_bounds
  simp only [cot_pi_9_17_lower, cot_pi_9_17_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_17_bounds
  simp only [cot_pi_10_17_lower, cot_pi_10_17_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_17_bounds
  simp only [cot_pi_11_17_lower, cot_pi_11_17_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_17_bounds
  simp only [cot_pi_12_17_lower, cot_pi_12_17_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_17_bounds
  simp only [cot_pi_13_17_lower, cot_pi_13_17_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_17_bounds
  simp only [cot_pi_14_17_lower, cot_pi_14_17_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_17_bounds
  simp only [cot_pi_15_17_lower, cot_pi_15_17_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_17_bounds
  simp only [cot_pi_16_17_lower, cot_pi_16_17_upper] at b_cot_16
  rw [cotangentSumVFormula_42_17_lower, cotangentSumVFormula_42_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1742_formula_bound :
  (((328922976269430917 / 8796093022208000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 42) ∧
  (vasyuninBEntryFormula 17 42 ≤ ((42104392762302826999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_17_42_bounds
  have b_Vkh := cotangentSumVFormula_42_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_17_42_lower, cotangentSumVFormula_17_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_17_lower, cotangentSumVFormula_42_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_42_unfold :
    cotangentSumVFormula 19 42 =
      ((19/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 19 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_19_42_lower : ℚ := 3328862787652213618417 / 879609302220800000000
def cotangentSumVFormula_19_42_upper : ℚ := 3328862805244980131583 / 879609302220800000000
theorem cotangentSumVFormula_19_42_bounds :
  ((cotangentSumVFormula_19_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 42 ∧
  cotangentSumVFormula 19 42 ≤ ((cotangentSumVFormula_19_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_19_42_lower, cotangentSumVFormula_19_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_19_unfold :
    cotangentSumVFormula 42 19 =
      ((4/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_42_19_lower : ℚ := -3132758945744026225333 / 879609302220800000000
def cotangentSumVFormula_42_19_upper : ℚ := -3132758928151751899667 / 879609302220800000000
theorem cotangentSumVFormula_42_19_bounds :
  ((cotangentSumVFormula_42_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 19 ∧
  cotangentSumVFormula 42 19 ≤ ((cotangentSumVFormula_42_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_19_unfold]
  have b_cot_1 := cot_pi_1_19_bounds
  simp only [cot_pi_1_19_lower, cot_pi_1_19_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_19_bounds
  simp only [cot_pi_2_19_lower, cot_pi_2_19_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_19_bounds
  simp only [cot_pi_3_19_lower, cot_pi_3_19_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_19_bounds
  simp only [cot_pi_4_19_lower, cot_pi_4_19_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_19_bounds
  simp only [cot_pi_5_19_lower, cot_pi_5_19_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_19_bounds
  simp only [cot_pi_6_19_lower, cot_pi_6_19_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_19_bounds
  simp only [cot_pi_7_19_lower, cot_pi_7_19_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_19_bounds
  simp only [cot_pi_8_19_lower, cot_pi_8_19_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_19_bounds
  simp only [cot_pi_9_19_lower, cot_pi_9_19_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_19_bounds
  simp only [cot_pi_10_19_lower, cot_pi_10_19_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_19_bounds
  simp only [cot_pi_11_19_lower, cot_pi_11_19_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_19_bounds
  simp only [cot_pi_12_19_lower, cot_pi_12_19_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_19_bounds
  simp only [cot_pi_13_19_lower, cot_pi_13_19_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_19_bounds
  simp only [cot_pi_14_19_lower, cot_pi_14_19_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_19_bounds
  simp only [cot_pi_15_19_lower, cot_pi_15_19_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_19_bounds
  simp only [cot_pi_16_19_lower, cot_pi_16_19_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_19_bounds
  simp only [cot_pi_17_19_lower, cot_pi_17_19_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_19_bounds
  simp only [cot_pi_18_19_lower, cot_pi_18_19_upper] at b_cot_18
  rw [cotangentSumVFormula_42_19_lower, cotangentSumVFormula_42_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1942_formula_bound :
  (((5110467850781254047 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 42) ∧
  (vasyuninBEntryFormula 19 42 ≤ ((10221498651516382531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_19_42_bounds
  have b_Vkh := cotangentSumVFormula_42_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_19_42_lower, cotangentSumVFormula_19_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_19_lower, cotangentSumVFormula_42_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_42_unfold :
    cotangentSumVFormula 23 42 =
      ((23/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 23 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_23_42_lower : ℚ := -1664431402622472682979 / 439804651110400000000
def cotangentSumVFormula_23_42_upper : ℚ := -1664431393826107785771 / 439804651110400000000
theorem cotangentSumVFormula_23_42_bounds :
  ((cotangentSumVFormula_23_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 42 ∧
  cotangentSumVFormula 23 42 ≤ ((cotangentSumVFormula_23_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_23_42_lower, cotangentSumVFormula_23_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_23_unfold :
    cotangentSumVFormula 42 23 =
      ((19/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_42_23_lower : ℚ := 2349067130519397629521 / 439804651110400000000
def cotangentSumVFormula_42_23_upper : ℚ := 2349067139315558620479 / 439804651110400000000
theorem cotangentSumVFormula_42_23_bounds :
  ((cotangentSumVFormula_42_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 23 ∧
  cotangentSumVFormula 42 23 ≤ ((cotangentSumVFormula_42_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_23_unfold]
  have b_cot_1 := cot_pi_1_23_bounds
  simp only [cot_pi_1_23_lower, cot_pi_1_23_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_23_bounds
  simp only [cot_pi_2_23_lower, cot_pi_2_23_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_23_bounds
  simp only [cot_pi_3_23_lower, cot_pi_3_23_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_23_bounds
  simp only [cot_pi_4_23_lower, cot_pi_4_23_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_23_bounds
  simp only [cot_pi_5_23_lower, cot_pi_5_23_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_23_bounds
  simp only [cot_pi_6_23_lower, cot_pi_6_23_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_23_bounds
  simp only [cot_pi_7_23_lower, cot_pi_7_23_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_23_bounds
  simp only [cot_pi_8_23_lower, cot_pi_8_23_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_23_bounds
  simp only [cot_pi_9_23_lower, cot_pi_9_23_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_23_bounds
  simp only [cot_pi_10_23_lower, cot_pi_10_23_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_23_bounds
  simp only [cot_pi_11_23_lower, cot_pi_11_23_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_23_bounds
  simp only [cot_pi_12_23_lower, cot_pi_12_23_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_23_bounds
  simp only [cot_pi_13_23_lower, cot_pi_13_23_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_23_bounds
  simp only [cot_pi_14_23_lower, cot_pi_14_23_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_23_bounds
  simp only [cot_pi_15_23_lower, cot_pi_15_23_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_23_bounds
  simp only [cot_pi_16_23_lower, cot_pi_16_23_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_23_bounds
  simp only [cot_pi_17_23_lower, cot_pi_17_23_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_23_bounds
  simp only [cot_pi_18_23_lower, cot_pi_18_23_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_23_bounds
  simp only [cot_pi_19_23_lower, cot_pi_19_23_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_23_bounds
  simp only [cot_pi_20_23_lower, cot_pi_20_23_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_23_bounds
  simp only [cot_pi_21_23_lower, cot_pi_21_23_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_23_bounds
  simp only [cot_pi_22_23_lower, cot_pi_22_23_upper] at b_cot_22
  rw [cotangentSumVFormula_42_23_lower, cotangentSumVFormula_42_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2342_formula_bound :
  (((38234714362410235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 42) ∧
  (vasyuninBEntryFormula 23 42 ≤ ((38236966162225451999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_23_42_bounds
  have b_Vkh := cotangentSumVFormula_42_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_23_42_lower, cotangentSumVFormula_23_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_23_lower, cotangentSumVFormula_42_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_25_42_unfold :
    cotangentSumVFormula 25 42 =
      ((25/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 25 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_25_42_lower : ℚ := 1349531636300870285771 / 439804651110400000000
def cotangentSumVFormula_25_42_upper : ℚ := 1349531645097230495479 / 439804651110400000000
theorem cotangentSumVFormula_25_42_bounds :
  ((cotangentSumVFormula_25_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 42 ∧
  cotangentSumVFormula 25 42 ≤ ((cotangentSumVFormula_25_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_25_42_lower, cotangentSumVFormula_25_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_25_unfold :
    cotangentSumVFormula 42 25 =
      ((17/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((19/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((11/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((12/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((21/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((22/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((14/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((24/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 42 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_42_25_lower : ℚ := -87189090063071393401 / 109951162777600000000
def cotangentSumVFormula_42_25_upper : ℚ := -87189087864027825349 / 109951162777600000000
theorem cotangentSumVFormula_42_25_bounds :
  ((cotangentSumVFormula_42_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 25 ∧
  cotangentSumVFormula 42 25 ≤ ((cotangentSumVFormula_42_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_25_unfold]
  have b_cot_1 := cot_pi_1_25_bounds
  simp only [cot_pi_1_25_lower, cot_pi_1_25_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_25_bounds
  simp only [cot_pi_2_25_lower, cot_pi_2_25_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_25_bounds
  simp only [cot_pi_3_25_lower, cot_pi_3_25_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_25_bounds
  simp only [cot_pi_4_25_lower, cot_pi_4_25_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_25_bounds
  simp only [cot_pi_5_25_lower, cot_pi_5_25_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_25_bounds
  simp only [cot_pi_6_25_lower, cot_pi_6_25_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_25_bounds
  simp only [cot_pi_7_25_lower, cot_pi_7_25_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_25_bounds
  simp only [cot_pi_8_25_lower, cot_pi_8_25_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_25_bounds
  simp only [cot_pi_9_25_lower, cot_pi_9_25_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_25_bounds
  simp only [cot_pi_10_25_lower, cot_pi_10_25_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_25_bounds
  simp only [cot_pi_11_25_lower, cot_pi_11_25_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_25_bounds
  simp only [cot_pi_12_25_lower, cot_pi_12_25_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_25_bounds
  simp only [cot_pi_13_25_lower, cot_pi_13_25_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_25_bounds
  simp only [cot_pi_14_25_lower, cot_pi_14_25_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_25_bounds
  simp only [cot_pi_15_25_lower, cot_pi_15_25_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_25_bounds
  simp only [cot_pi_16_25_lower, cot_pi_16_25_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_25_bounds
  simp only [cot_pi_17_25_lower, cot_pi_17_25_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_25_bounds
  simp only [cot_pi_18_25_lower, cot_pi_18_25_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_25_bounds
  simp only [cot_pi_19_25_lower, cot_pi_19_25_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_25_bounds
  simp only [cot_pi_20_25_lower, cot_pi_20_25_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_25_bounds
  simp only [cot_pi_21_25_lower, cot_pi_21_25_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_25_bounds
  simp only [cot_pi_22_25_lower, cot_pi_22_25_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_25_bounds
  simp only [cot_pi_23_25_lower, cot_pi_23_25_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_25_bounds
  simp only [cot_pi_24_25_lower, cot_pi_24_25_upper] at b_cot_24
  rw [cotangentSumVFormula_42_25_lower, cotangentSumVFormula_42_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2542_formula_bound :
  (((36722580160241110501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 42) ∧
  (vasyuninBEntryFormula 25 42 ≤ ((18362415980028124437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_25_42_bounds
  have b_Vkh := cotangentSumVFormula_42_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_25_42_lower, cotangentSumVFormula_25_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_25_lower, cotangentSumVFormula_42_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_42_unfold :
    cotangentSumVFormula 29 42 =
      ((29/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 29 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_29_42_lower : ℚ := 2341522198474481533709 / 1759218604441600000000
def cotangentSumVFormula_29_42_upper : ℚ := 2341522233659846591291 / 1759218604441600000000
theorem cotangentSumVFormula_29_42_bounds :
  ((cotangentSumVFormula_29_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 42 ∧
  cotangentSumVFormula 29 42 ≤ ((cotangentSumVFormula_29_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_29_42_lower, cotangentSumVFormula_29_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_29_unfold :
    cotangentSumVFormula 42 29 =
      ((13/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 42 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_42_29_lower : ℚ := 3042103078162929189959 / 1759218604441600000000
def cotangentSumVFormula_42_29_upper : ℚ := 3042103113347708310041 / 1759218604441600000000
theorem cotangentSumVFormula_42_29_bounds :
  ((cotangentSumVFormula_42_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 29 ∧
  cotangentSumVFormula 42 29 ≤ ((cotangentSumVFormula_42_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_29_unfold]
  have b_cot_1 := cot_pi_1_29_bounds
  simp only [cot_pi_1_29_lower, cot_pi_1_29_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_29_bounds
  simp only [cot_pi_2_29_lower, cot_pi_2_29_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_29_bounds
  simp only [cot_pi_3_29_lower, cot_pi_3_29_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_29_bounds
  simp only [cot_pi_4_29_lower, cot_pi_4_29_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_29_bounds
  simp only [cot_pi_5_29_lower, cot_pi_5_29_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_29_bounds
  simp only [cot_pi_6_29_lower, cot_pi_6_29_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_29_bounds
  simp only [cot_pi_7_29_lower, cot_pi_7_29_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_29_bounds
  simp only [cot_pi_8_29_lower, cot_pi_8_29_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_29_bounds
  simp only [cot_pi_9_29_lower, cot_pi_9_29_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_29_bounds
  simp only [cot_pi_10_29_lower, cot_pi_10_29_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_29_bounds
  simp only [cot_pi_11_29_lower, cot_pi_11_29_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_29_bounds
  simp only [cot_pi_12_29_lower, cot_pi_12_29_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_29_bounds
  simp only [cot_pi_13_29_lower, cot_pi_13_29_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_29_bounds
  simp only [cot_pi_14_29_lower, cot_pi_14_29_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_29_bounds
  simp only [cot_pi_15_29_lower, cot_pi_15_29_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_29_bounds
  simp only [cot_pi_16_29_lower, cot_pi_16_29_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_29_bounds
  simp only [cot_pi_17_29_lower, cot_pi_17_29_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_29_bounds
  simp only [cot_pi_18_29_lower, cot_pi_18_29_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_29_bounds
  simp only [cot_pi_19_29_lower, cot_pi_19_29_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_29_bounds
  simp only [cot_pi_20_29_lower, cot_pi_20_29_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_29_bounds
  simp only [cot_pi_21_29_lower, cot_pi_21_29_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_29_bounds
  simp only [cot_pi_22_29_lower, cot_pi_22_29_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_29_bounds
  simp only [cot_pi_23_29_lower, cot_pi_23_29_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_29_bounds
  simp only [cot_pi_24_29_lower, cot_pi_24_29_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_29_bounds
  simp only [cot_pi_25_29_lower, cot_pi_25_29_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_29_bounds
  simp only [cot_pi_26_29_lower, cot_pi_26_29_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_29_bounds
  simp only [cot_pi_27_29_lower, cot_pi_27_29_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_29_bounds
  simp only [cot_pi_28_29_lower, cot_pi_28_29_upper] at b_cot_28
  rw [cotangentSumVFormula_42_29_lower, cotangentSumVFormula_42_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2942_formula_bound :
  (((138797478084082520129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 42) ∧
  (vasyuninBEntryFormula 29 42 ≤ ((138806485283342292371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_29_42_bounds
  have b_Vkh := cotangentSumVFormula_42_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_29_42_lower, cotangentSumVFormula_29_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_29_lower, cotangentSumVFormula_42_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_42_unfold :
    cotangentSumVFormula 31 42 =
      ((31/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 31 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_31_42_lower : ℚ := 370196059608309420487 / 54975581388800000000
def cotangentSumVFormula_31_42_upper : ℚ := 1480784242831404896177 / 219902325555200000000
theorem cotangentSumVFormula_31_42_bounds :
  ((cotangentSumVFormula_31_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 42 ∧
  cotangentSumVFormula 31 42 ≤ ((cotangentSumVFormula_31_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_31_42_lower, cotangentSumVFormula_31_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_31_unfold :
    cotangentSumVFormula 42 31 =
      ((11/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 42 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_42_31_lower : ℚ := -3036187542087313725333 / 879609302220800000000
def cotangentSumVFormula_42_31_upper : ℚ := -3036187524494833930917 / 879609302220800000000
theorem cotangentSumVFormula_42_31_bounds :
  ((cotangentSumVFormula_42_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 31 ∧
  cotangentSumVFormula 42 31 ≤ ((cotangentSumVFormula_42_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_31_unfold]
  have b_cot_1 := cot_pi_1_31_bounds
  simp only [cot_pi_1_31_lower, cot_pi_1_31_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_31_bounds
  simp only [cot_pi_2_31_lower, cot_pi_2_31_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_31_bounds
  simp only [cot_pi_3_31_lower, cot_pi_3_31_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_31_bounds
  simp only [cot_pi_4_31_lower, cot_pi_4_31_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_31_bounds
  simp only [cot_pi_5_31_lower, cot_pi_5_31_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_31_bounds
  simp only [cot_pi_6_31_lower, cot_pi_6_31_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_31_bounds
  simp only [cot_pi_7_31_lower, cot_pi_7_31_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_31_bounds
  simp only [cot_pi_8_31_lower, cot_pi_8_31_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_31_bounds
  simp only [cot_pi_9_31_lower, cot_pi_9_31_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_31_bounds
  simp only [cot_pi_10_31_lower, cot_pi_10_31_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_31_bounds
  simp only [cot_pi_11_31_lower, cot_pi_11_31_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_31_bounds
  simp only [cot_pi_12_31_lower, cot_pi_12_31_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_31_bounds
  simp only [cot_pi_13_31_lower, cot_pi_13_31_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_31_bounds
  simp only [cot_pi_14_31_lower, cot_pi_14_31_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_31_bounds
  simp only [cot_pi_15_31_lower, cot_pi_15_31_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_31_bounds
  simp only [cot_pi_16_31_lower, cot_pi_16_31_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_31_bounds
  simp only [cot_pi_17_31_lower, cot_pi_17_31_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_31_bounds
  simp only [cot_pi_18_31_lower, cot_pi_18_31_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_31_bounds
  simp only [cot_pi_19_31_lower, cot_pi_19_31_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_31_bounds
  simp only [cot_pi_20_31_lower, cot_pi_20_31_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_31_bounds
  simp only [cot_pi_21_31_lower, cot_pi_21_31_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_31_bounds
  simp only [cot_pi_22_31_lower, cot_pi_22_31_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_31_bounds
  simp only [cot_pi_23_31_lower, cot_pi_23_31_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_31_bounds
  simp only [cot_pi_24_31_lower, cot_pi_24_31_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_31_bounds
  simp only [cot_pi_25_31_lower, cot_pi_25_31_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_31_bounds
  simp only [cot_pi_26_31_lower, cot_pi_26_31_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_31_bounds
  simp only [cot_pi_27_31_lower, cot_pi_27_31_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_31_bounds
  simp only [cot_pi_28_31_lower, cot_pi_28_31_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_31_bounds
  simp only [cot_pi_29_31_lower, cot_pi_29_31_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_31_bounds
  simp only [cot_pi_30_31_lower, cot_pi_30_31_upper] at b_cot_30
  rw [cotangentSumVFormula_42_31_lower, cotangentSumVFormula_42_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3142_formula_bound :
  (((67773820391481205377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 42) ∧
  (vasyuninBEntryFormula 31 42 ≤ ((67778323991111169623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_31_42_bounds
  have b_Vkh := cotangentSumVFormula_42_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_31_42_lower, cotangentSumVFormula_31_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_31_lower, cotangentSumVFormula_42_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_42_unfold :
    cotangentSumVFormula 37 42 =
      ((37/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_37_42_lower : ℚ := 1440014984491442669099 / 109951162777600000000
def cotangentSumVFormula_37_42_upper : ℚ := 1440014986690518268401 / 109951162777600000000
theorem cotangentSumVFormula_37_42_bounds :
  ((cotangentSumVFormula_37_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 42 ∧
  cotangentSumVFormula 37 42 ≤ ((cotangentSumVFormula_37_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_37_42_lower, cotangentSumVFormula_37_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_37_unfold :
    cotangentSumVFormula 42 37 =
      ((5/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 42 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_42_37_lower : ℚ := -2247747601022716614927 / 219902325555200000000
def cotangentSumVFormula_42_37_upper : ℚ := -2247747596624577916323 / 219902325555200000000
theorem cotangentSumVFormula_42_37_bounds :
  ((cotangentSumVFormula_42_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 37 ∧
  cotangentSumVFormula 42 37 ≤ ((cotangentSumVFormula_42_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_37_unfold]
  have b_cot_1 := cot_pi_1_37_bounds
  simp only [cot_pi_1_37_lower, cot_pi_1_37_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_37_bounds
  simp only [cot_pi_2_37_lower, cot_pi_2_37_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_37_bounds
  simp only [cot_pi_3_37_lower, cot_pi_3_37_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_37_bounds
  simp only [cot_pi_4_37_lower, cot_pi_4_37_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_37_bounds
  simp only [cot_pi_5_37_lower, cot_pi_5_37_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_37_bounds
  simp only [cot_pi_6_37_lower, cot_pi_6_37_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_37_bounds
  simp only [cot_pi_7_37_lower, cot_pi_7_37_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_37_bounds
  simp only [cot_pi_8_37_lower, cot_pi_8_37_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_37_bounds
  simp only [cot_pi_9_37_lower, cot_pi_9_37_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_37_bounds
  simp only [cot_pi_10_37_lower, cot_pi_10_37_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_37_bounds
  simp only [cot_pi_11_37_lower, cot_pi_11_37_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_37_bounds
  simp only [cot_pi_12_37_lower, cot_pi_12_37_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_37_bounds
  simp only [cot_pi_13_37_lower, cot_pi_13_37_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_37_bounds
  simp only [cot_pi_14_37_lower, cot_pi_14_37_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_37_bounds
  simp only [cot_pi_15_37_lower, cot_pi_15_37_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_37_bounds
  simp only [cot_pi_16_37_lower, cot_pi_16_37_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_37_bounds
  simp only [cot_pi_17_37_lower, cot_pi_17_37_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_37_bounds
  simp only [cot_pi_18_37_lower, cot_pi_18_37_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_37_bounds
  simp only [cot_pi_19_37_lower, cot_pi_19_37_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_37_bounds
  simp only [cot_pi_20_37_lower, cot_pi_20_37_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_37_bounds
  simp only [cot_pi_21_37_lower, cot_pi_21_37_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_37_bounds
  simp only [cot_pi_22_37_lower, cot_pi_22_37_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_37_bounds
  simp only [cot_pi_23_37_lower, cot_pi_23_37_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_37_bounds
  simp only [cot_pi_24_37_lower, cot_pi_24_37_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_37_bounds
  simp only [cot_pi_25_37_lower, cot_pi_25_37_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_37_bounds
  simp only [cot_pi_26_37_lower, cot_pi_26_37_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_37_bounds
  simp only [cot_pi_27_37_lower, cot_pi_27_37_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_37_bounds
  simp only [cot_pi_28_37_lower, cot_pi_28_37_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_37_bounds
  simp only [cot_pi_29_37_lower, cot_pi_29_37_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_37_bounds
  simp only [cot_pi_30_37_lower, cot_pi_30_37_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_37_bounds
  simp only [cot_pi_31_37_lower, cot_pi_31_37_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_37_bounds
  simp only [cot_pi_32_37_lower, cot_pi_32_37_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_37_bounds
  simp only [cot_pi_33_37_lower, cot_pi_33_37_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_37_bounds
  simp only [cot_pi_34_37_lower, cot_pi_34_37_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_37_bounds
  simp only [cot_pi_35_37_lower, cot_pi_35_37_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_37_bounds
  simp only [cot_pi_36_37_lower, cot_pi_36_37_upper] at b_cot_36
  rw [cotangentSumVFormula_42_37_lower, cotangentSumVFormula_42_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3742_formula_bound :
  (((130300675319739145129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 42) ∧
  (vasyuninBEntryFormula 37 42 ≤ ((130309682518998354871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_37_42_bounds
  have b_Vkh := cotangentSumVFormula_42_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_37_42_lower, cotangentSumVFormula_37_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_37_lower, cotangentSumVFormula_42_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_42_unfold :
    cotangentSumVFormula 41 42 =
      ((41/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_41_42_lower : ℚ := 919069348504315452431 / 27487790694400000000
def cotangentSumVFormula_41_42_upper : ℚ := 229767337263522211111 / 6871947673600000000
theorem cotangentSumVFormula_41_42_bounds :
  ((cotangentSumVFormula_41_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 42 ∧
  cotangentSumVFormula 41 42 ≤ ((cotangentSumVFormula_41_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_42_unfold]
  have b_cot_1 := cot_pi_1_42_bounds
  simp only [cot_pi_1_42_lower, cot_pi_1_42_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_42_bounds
  simp only [cot_pi_2_42_lower, cot_pi_2_42_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_42_bounds
  simp only [cot_pi_3_42_lower, cot_pi_3_42_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_42_bounds
  simp only [cot_pi_4_42_lower, cot_pi_4_42_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_42_bounds
  simp only [cot_pi_5_42_lower, cot_pi_5_42_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_42_bounds
  simp only [cot_pi_6_42_lower, cot_pi_6_42_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_42_bounds
  simp only [cot_pi_7_42_lower, cot_pi_7_42_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_42_bounds
  simp only [cot_pi_8_42_lower, cot_pi_8_42_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_42_bounds
  simp only [cot_pi_9_42_lower, cot_pi_9_42_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_42_bounds
  simp only [cot_pi_10_42_lower, cot_pi_10_42_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_42_bounds
  simp only [cot_pi_11_42_lower, cot_pi_11_42_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_42_bounds
  simp only [cot_pi_12_42_lower, cot_pi_12_42_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_42_bounds
  simp only [cot_pi_13_42_lower, cot_pi_13_42_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_42_bounds
  simp only [cot_pi_14_42_lower, cot_pi_14_42_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_42_bounds
  simp only [cot_pi_15_42_lower, cot_pi_15_42_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_42_bounds
  simp only [cot_pi_16_42_lower, cot_pi_16_42_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_42_bounds
  simp only [cot_pi_17_42_lower, cot_pi_17_42_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_42_bounds
  simp only [cot_pi_18_42_lower, cot_pi_18_42_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_42_bounds
  simp only [cot_pi_19_42_lower, cot_pi_19_42_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_42_bounds
  simp only [cot_pi_20_42_lower, cot_pi_20_42_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_42_bounds
  simp only [cot_pi_21_42_lower, cot_pi_21_42_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_42_bounds
  simp only [cot_pi_22_42_lower, cot_pi_22_42_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_42_bounds
  simp only [cot_pi_23_42_lower, cot_pi_23_42_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_42_bounds
  simp only [cot_pi_24_42_lower, cot_pi_24_42_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_42_bounds
  simp only [cot_pi_25_42_lower, cot_pi_25_42_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_42_bounds
  simp only [cot_pi_26_42_lower, cot_pi_26_42_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_42_bounds
  simp only [cot_pi_27_42_lower, cot_pi_27_42_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_42_bounds
  simp only [cot_pi_28_42_lower, cot_pi_28_42_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_42_bounds
  simp only [cot_pi_29_42_lower, cot_pi_29_42_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_42_bounds
  simp only [cot_pi_30_42_lower, cot_pi_30_42_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_42_bounds
  simp only [cot_pi_31_42_lower, cot_pi_31_42_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_42_bounds
  simp only [cot_pi_32_42_lower, cot_pi_32_42_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_42_bounds
  simp only [cot_pi_33_42_lower, cot_pi_33_42_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_42_bounds
  simp only [cot_pi_34_42_lower, cot_pi_34_42_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_42_bounds
  simp only [cot_pi_35_42_lower, cot_pi_35_42_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_42_bounds
  simp only [cot_pi_36_42_lower, cot_pi_36_42_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_42_bounds
  simp only [cot_pi_37_42_lower, cot_pi_37_42_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_42_bounds
  simp only [cot_pi_38_42_lower, cot_pi_38_42_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_42_bounds
  simp only [cot_pi_39_42_lower, cot_pi_39_42_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_42_bounds
  simp only [cot_pi_40_42_lower, cot_pi_40_42_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_42_bounds
  simp only [cot_pi_41_42_lower, cot_pi_41_42_upper] at b_cot_41
  rw [cotangentSumVFormula_41_42_lower, cotangentSumVFormula_41_42_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_42_41_unfold :
    cotangentSumVFormula 42 41 =
      ((1/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((2/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((3/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((4/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((5/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((6/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((8/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((9/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 42 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_42_41_lower : ℚ := -888753186278601735069 / 27487790694400000000
def cotangentSumVFormula_42_41_upper : ℚ := -111094148216103933507 / 3435973836800000000
theorem cotangentSumVFormula_42_41_bounds :
  ((cotangentSumVFormula_42_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 41 ∧
  cotangentSumVFormula 42 41 ≤ ((cotangentSumVFormula_42_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_41_unfold]
  have b_cot_1 := cot_pi_1_41_bounds
  simp only [cot_pi_1_41_lower, cot_pi_1_41_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_41_bounds
  simp only [cot_pi_2_41_lower, cot_pi_2_41_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_41_bounds
  simp only [cot_pi_3_41_lower, cot_pi_3_41_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_41_bounds
  simp only [cot_pi_4_41_lower, cot_pi_4_41_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_41_bounds
  simp only [cot_pi_5_41_lower, cot_pi_5_41_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_41_bounds
  simp only [cot_pi_6_41_lower, cot_pi_6_41_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_41_bounds
  simp only [cot_pi_7_41_lower, cot_pi_7_41_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_41_bounds
  simp only [cot_pi_8_41_lower, cot_pi_8_41_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_41_bounds
  simp only [cot_pi_9_41_lower, cot_pi_9_41_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_41_bounds
  simp only [cot_pi_10_41_lower, cot_pi_10_41_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_41_bounds
  simp only [cot_pi_11_41_lower, cot_pi_11_41_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_41_bounds
  simp only [cot_pi_12_41_lower, cot_pi_12_41_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_41_bounds
  simp only [cot_pi_13_41_lower, cot_pi_13_41_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_41_bounds
  simp only [cot_pi_14_41_lower, cot_pi_14_41_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_41_bounds
  simp only [cot_pi_15_41_lower, cot_pi_15_41_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_41_bounds
  simp only [cot_pi_16_41_lower, cot_pi_16_41_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_41_bounds
  simp only [cot_pi_17_41_lower, cot_pi_17_41_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_41_bounds
  simp only [cot_pi_18_41_lower, cot_pi_18_41_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_41_bounds
  simp only [cot_pi_19_41_lower, cot_pi_19_41_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_41_bounds
  simp only [cot_pi_20_41_lower, cot_pi_20_41_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_41_bounds
  simp only [cot_pi_21_41_lower, cot_pi_21_41_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_41_bounds
  simp only [cot_pi_22_41_lower, cot_pi_22_41_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_41_bounds
  simp only [cot_pi_23_41_lower, cot_pi_23_41_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_41_bounds
  simp only [cot_pi_24_41_lower, cot_pi_24_41_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_41_bounds
  simp only [cot_pi_25_41_lower, cot_pi_25_41_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_41_bounds
  simp only [cot_pi_26_41_lower, cot_pi_26_41_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_41_bounds
  simp only [cot_pi_27_41_lower, cot_pi_27_41_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_41_bounds
  simp only [cot_pi_28_41_lower, cot_pi_28_41_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_41_bounds
  simp only [cot_pi_29_41_lower, cot_pi_29_41_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_41_bounds
  simp only [cot_pi_30_41_lower, cot_pi_30_41_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_41_bounds
  simp only [cot_pi_31_41_lower, cot_pi_31_41_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_41_bounds
  simp only [cot_pi_32_41_lower, cot_pi_32_41_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_41_bounds
  simp only [cot_pi_33_41_lower, cot_pi_33_41_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_41_bounds
  simp only [cot_pi_34_41_lower, cot_pi_34_41_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_41_bounds
  simp only [cot_pi_35_41_lower, cot_pi_35_41_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_41_bounds
  simp only [cot_pi_36_41_lower, cot_pi_36_41_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_41_bounds
  simp only [cot_pi_37_41_lower, cot_pi_37_41_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_41_bounds
  simp only [cot_pi_38_41_lower, cot_pi_38_41_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_41_bounds
  simp only [cot_pi_39_41_lower, cot_pi_39_41_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_41_bounds
  simp only [cot_pi_40_41_lower, cot_pi_40_41_upper] at b_cot_40
  rw [cotangentSumVFormula_42_41_lower, cotangentSumVFormula_42_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4142_formula_bound :
  (((132260555437053270129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 42) ∧
  (vasyuninBEntryFormula 41 42 ≤ ((132269562636313104871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 42 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log42 := prim_log_42_bounds
  have b_Vhk := cotangentSumVFormula_41_42_bounds
  have b_Vkh := cotangentSumVFormula_42_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [cotangentSumVFormula_41_42_lower, cotangentSumVFormula_41_42_upper] at b_Vhk
  simp only [cotangentSumVFormula_42_41_lower, cotangentSumVFormula_42_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_43_unfold :
    cotangentSumVFormula 1 43 =
      ((1/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 1 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_1_43_lower : ℚ := -1899187841898131204513 / 54975581388800000000
def cotangentSumVFormula_1_43_upper : ℚ := -1899187840798574264237 / 54975581388800000000
theorem cotangentSumVFormula_1_43_bounds :
  ((cotangentSumVFormula_1_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 43 ∧
  cotangentSumVFormula 1 43 ≤ ((cotangentSumVFormula_1_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_1_43_lower, cotangentSumVFormula_1_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_1_unfold :
    cotangentSumVFormula 43 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_43_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_43_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_43_1_bounds :
  ((cotangentSumVFormula_43_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 1 ∧
  cotangentSumVFormula 43 1 ≤ ((cotangentSumVFormula_43_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_1_unfold]
  rw [cotangentSumVFormula_43_1_lower, cotangentSumVFormula_43_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_143_formula_bound :
  (((78919705274676891751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 43) ∧
  (vasyuninBEntryFormula 1 43 ≤ ((78921957074529108249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_43_bounds
  have b_Vkh := cotangentSumVFormula_43_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_1_43_lower, cotangentSumVFormula_1_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_1_lower, cotangentSumVFormula_43_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_43_unfold :
    cotangentSumVFormula 2 43 =
      ((2/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 2 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_2_43_lower : ℚ := -2789896565158104205901 / 109951162777600000000
def cotangentSumVFormula_2_43_upper : ℚ := -2789896562958988762849 / 109951162777600000000
theorem cotangentSumVFormula_2_43_bounds :
  ((cotangentSumVFormula_2_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 43 ∧
  cotangentSumVFormula 2 43 ≤ ((cotangentSumVFormula_2_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_2_43_lower, cotangentSumVFormula_2_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_2_unfold :
    cotangentSumVFormula 43 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_43_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_43_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_43_2_bounds :
  ((cotangentSumVFormula_43_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 2 ∧
  cotangentSumVFormula 43 2 ≤ ((cotangentSumVFormula_43_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_43_2_lower, cotangentSumVFormula_43_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_243_formula_bound :
  (((139481606763358299127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 43) ∧
  (vasyuninBEntryFormula 2 43 ≤ ((139486110363023950873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_43_bounds
  have b_Vkh := cotangentSumVFormula_43_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_2_43_lower, cotangentSumVFormula_2_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_2_lower, cotangentSumVFormula_43_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_43_unfold :
    cotangentSumVFormula 3 43 =
      ((3/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 3 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_3_43_lower : ℚ := -548321608165038453819 / 27487790694400000000
def cotangentSumVFormula_3_43_upper : ℚ := -1096643215230520357987 / 54975581388800000000
theorem cotangentSumVFormula_3_43_bounds :
  ((cotangentSumVFormula_3_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 43 ∧
  cotangentSumVFormula 3 43 ≤ ((cotangentSumVFormula_3_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_3_43_lower, cotangentSumVFormula_3_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_3_unfold :
    cotangentSumVFormula 43 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_43_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_43_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_43_3_bounds :
  ((cotangentSumVFormula_43_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 3 ∧
  cotangentSumVFormula 43 3 ≤ ((cotangentSumVFormula_43_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_43_3_lower, cotangentSumVFormula_43_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_343_formula_bound :
  (((128816828141222174127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 43) ∧
  (vasyuninBEntryFormula 3 43 ≤ ((128821331740874575873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_43_bounds
  have b_Vkh := cotangentSumVFormula_43_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_3_43_lower, cotangentSumVFormula_3_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_3_lower, cotangentSumVFormula_43_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_43_unfold :
    cotangentSumVFormula 4 43 =
      ((4/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 4 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_4_43_lower : ℚ := -1871354990201078424651 / 109951162777600000000
def cotangentSumVFormula_4_43_upper : ℚ := -1871354988001965325349 / 109951162777600000000
theorem cotangentSumVFormula_4_43_bounds :
  ((cotangentSumVFormula_4_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 43 ∧
  cotangentSumVFormula 4 43 ≤ ((cotangentSumVFormula_4_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_4_43_lower, cotangentSumVFormula_4_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_4_unfold :
    cotangentSumVFormula 43 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_43_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_43_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_43_4_bounds :
  ((cotangentSumVFormula_43_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 4 ∧
  cotangentSumVFormula 43 4 ≤ ((cotangentSumVFormula_43_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_43_4_lower, cotangentSumVFormula_43_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_443_formula_bound :
  (((121283860756136424127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 43) ∧
  (vasyuninBEntryFormula 4 43 ≤ ((121288364355782200873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_43_bounds
  have b_Vkh := cotangentSumVFormula_43_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_4_43_lower, cotangentSumVFormula_4_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_4_lower, cotangentSumVFormula_43_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_43_unfold :
    cotangentSumVFormula 5 43 =
      ((5/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 5 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_5_43_lower : ℚ := -1523425347521405768401 / 109951162777600000000
def cotangentSumVFormula_5_43_upper : ℚ := -1523425345322294231599 / 109951162777600000000
theorem cotangentSumVFormula_5_43_bounds :
  ((cotangentSumVFormula_5_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 43 ∧
  cotangentSumVFormula 5 43 ≤ ((cotangentSumVFormula_5_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_5_43_lower, cotangentSumVFormula_5_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_5_unfold :
    cotangentSumVFormula 43 5 =
      ((3/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_43_5_lower : ℚ := 2260935262917356492469 / 28147497671065600000000
def cotangentSumVFormula_43_5_upper : ℚ := 2260935825867424757531 / 28147497671065600000000
theorem cotangentSumVFormula_43_5_bounds :
  ((cotangentSumVFormula_43_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 5 ∧
  cotangentSumVFormula 43 5 ≤ ((cotangentSumVFormula_43_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_43_5_lower, cotangentSumVFormula_43_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_543_formula_bound :
  (((115314448916430299127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 43) ∧
  (vasyuninBEntryFormula 5 43 ≤ ((115318952516072200873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_43_bounds
  have b_Vkh := cotangentSumVFormula_43_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_5_43_lower, cotangentSumVFormula_5_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_5_lower, cotangentSumVFormula_43_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_43_unfold :
    cotangentSumVFormula 6 43 =
      ((6/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 6 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_6_43_lower : ℚ := -2257714267322599427427 / 219902325555200000000
def cotangentSumVFormula_6_43_upper : ℚ := -2257714262924374791323 / 219902325555200000000
theorem cotangentSumVFormula_6_43_bounds :
  ((cotangentSumVFormula_6_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 43 ∧
  cotangentSumVFormula 6 43 ≤ ((cotangentSumVFormula_6_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_6_43_lower, cotangentSumVFormula_6_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_6_unfold :
    cotangentSumVFormula 43 6 =
      ((1/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((5/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_43_6_lower : ℚ := -2369932465546953622541 / 1759218604441600000000
def cotangentSumVFormula_43_6_upper : ℚ := -2369932430362564346209 / 1759218604441600000000
theorem cotangentSumVFormula_43_6_bounds :
  ((cotangentSumVFormula_43_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 6 ∧
  cotangentSumVFormula 43 6 ≤ ((cotangentSumVFormula_43_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_6_unfold]
  have b_cot_1 := cot_pi_1_6_bounds
  simp only [cot_pi_1_6_lower, cot_pi_1_6_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_6_bounds
  simp only [cot_pi_2_6_lower, cot_pi_2_6_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_6_bounds
  simp only [cot_pi_3_6_lower, cot_pi_3_6_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_6_bounds
  simp only [cot_pi_4_6_lower, cot_pi_4_6_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_6_bounds
  simp only [cot_pi_5_6_lower, cot_pi_5_6_upper] at b_cot_5
  rw [cotangentSumVFormula_43_6_lower, cotangentSumVFormula_43_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_643_formula_bound :
  (((865603458096658709 / 17592186044416000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 43) ∧
  (vasyuninBEntryFormula 6 43 ≤ ((27700436559002999437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_43_bounds
  have b_Vkh := cotangentSumVFormula_43_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_6_43_lower, cotangentSumVFormula_6_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_6_lower, cotangentSumVFormula_43_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_43_unfold :
    cotangentSumVFormula 7 43 =
      ((7/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 7 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_7_43_lower : ℚ := -3506335817518192995479 / 439804651110400000000
def cotangentSumVFormula_7_43_upper : ℚ := -3506335808721740598271 / 439804651110400000000
theorem cotangentSumVFormula_7_43_bounds :
  ((cotangentSumVFormula_7_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 43 ∧
  cotangentSumVFormula 7 43 ≤ ((cotangentSumVFormula_7_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_7_43_lower, cotangentSumVFormula_7_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_7_unfold :
    cotangentSumVFormula 43 7 =
      ((1/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_43_7_lower : ℚ := -3267942246185352841291 / 1759218604441600000000
def cotangentSumVFormula_43_7_upper : ℚ := -3267942211000966689959 / 1759218604441600000000
theorem cotangentSumVFormula_43_7_bounds :
  ((cotangentSumVFormula_43_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 7 ∧
  cotangentSumVFormula 43 7 ≤ ((cotangentSumVFormula_43_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_7_unfold]
  have b_cot_1 := cot_pi_1_7_bounds
  simp only [cot_pi_1_7_lower, cot_pi_1_7_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_7_bounds
  simp only [cot_pi_2_7_lower, cot_pi_2_7_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_7_bounds
  simp only [cot_pi_3_7_lower, cot_pi_3_7_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_7_bounds
  simp only [cot_pi_4_7_lower, cot_pi_4_7_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_7_bounds
  simp only [cot_pi_5_7_lower, cot_pi_5_7_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_7_bounds
  simp only [cot_pi_6_7_lower, cot_pi_6_7_upper] at b_cot_6
  rw [cotangentSumVFormula_43_7_lower, cotangentSumVFormula_43_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_743_formula_bound :
  (((106845217599539642877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 43) ∧
  (vasyuninBEntryFormula 7 43 ≤ ((106849721199177513373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_7_43_bounds
  have b_Vkh := cotangentSumVFormula_43_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_7_43_lower, cotangentSumVFormula_7_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_7_lower, cotangentSumVFormula_43_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_43_unfold :
    cotangentSumVFormula 8 43 =
      ((8/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 8 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_8_43_lower : ℚ := -1729451772364935364927 / 219902325555200000000
def cotangentSumVFormula_8_43_upper : ℚ := -1729451767966710728823 / 219902325555200000000
theorem cotangentSumVFormula_8_43_bounds :
  ((cotangentSumVFormula_8_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 43 ∧
  cotangentSumVFormula 8 43 ≤ ((cotangentSumVFormula_8_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_8_43_lower, cotangentSumVFormula_8_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_8_unfold :
    cotangentSumVFormula 43 8 =
      ((3/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_43_8_lower : ℚ := -728692222730972372541 / 1759218604441600000000
def cotangentSumVFormula_43_8_upper : ℚ := -728692187546586221209 / 1759218604441600000000
theorem cotangentSumVFormula_43_8_bounds :
  ((cotangentSumVFormula_43_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 8 ∧
  cotangentSumVFormula 43 8 ≤ ((cotangentSumVFormula_43_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_8_unfold]
  have b_cot_1 := cot_pi_1_8_bounds
  simp only [cot_pi_1_8_lower, cot_pi_1_8_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_8_bounds
  simp only [cot_pi_2_8_lower, cot_pi_2_8_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_8_bounds
  simp only [cot_pi_3_8_lower, cot_pi_3_8_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_8_bounds
  simp only [cot_pi_4_8_lower, cot_pi_4_8_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_8_bounds
  simp only [cot_pi_5_8_lower, cot_pi_5_8_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_8_bounds
  simp only [cot_pi_6_8_lower, cot_pi_6_8_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_8_bounds
  simp only [cot_pi_7_8_lower, cot_pi_7_8_upper] at b_cot_7
  rw [cotangentSumVFormula_43_8_lower, cotangentSumVFormula_43_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_843_formula_bound :
  (((102902887629403267877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 43) ∧
  (vasyuninBEntryFormula 8 43 ≤ ((102907391229039700873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_8_43_bounds
  have b_Vkh := cotangentSumVFormula_43_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_8_43_lower, cotangentSumVFormula_8_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_8_lower, cotangentSumVFormula_43_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_43_unfold :
    cotangentSumVFormula 9 43 =
      ((9/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 9 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_9_43_lower : ℚ := -1830739721924150989927 / 219902325555200000000
def cotangentSumVFormula_9_43_upper : ℚ := -1830739717525927916323 / 219902325555200000000
theorem cotangentSumVFormula_9_43_bounds :
  ((cotangentSumVFormula_9_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 43 ∧
  cotangentSumVFormula 9 43 ≤ ((cotangentSumVFormula_9_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_9_43_lower, cotangentSumVFormula_9_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_9_unfold :
    cotangentSumVFormula 43 9 =
      ((7/9 : ℚ) : ℝ) * cotangentTermV 1 9    + 
      ((5/9 : ℚ) : ℝ) * cotangentTermV 2 9    + 
      ((3/9 : ℚ) : ℝ) * cotangentTermV 3 9    + 
      ((1/9 : ℚ) : ℝ) * cotangentTermV 4 9    + 
      ((8/9 : ℚ) : ℝ) * cotangentTermV 5 9    + 
      ((6/9 : ℚ) : ℝ) * cotangentTermV 6 9    + 
      ((4/9 : ℚ) : ℝ) * cotangentTermV 7 9    + 
      ((2/9 : ℚ) : ℝ) * cotangentTermV 8 9 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_9]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_43_9_lower : ℚ := 584588387572393723271 / 439804651110400000000
def cotangentSumVFormula_43_9_upper : ℚ := 1169176792736990287833 / 879609302220800000000
theorem cotangentSumVFormula_43_9_bounds :
  ((cotangentSumVFormula_43_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 9 ∧
  cotangentSumVFormula 43 9 ≤ ((cotangentSumVFormula_43_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_9_unfold]
  have b_cot_1 := cot_pi_1_9_bounds
  simp only [cot_pi_1_9_lower, cot_pi_1_9_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_9_bounds
  simp only [cot_pi_2_9_lower, cot_pi_2_9_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_9_bounds
  simp only [cot_pi_3_9_lower, cot_pi_3_9_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_9_bounds
  simp only [cot_pi_4_9_lower, cot_pi_4_9_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_9_bounds
  simp only [cot_pi_5_9_lower, cot_pi_5_9_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_9_bounds
  simp only [cot_pi_6_9_lower, cot_pi_6_9_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_9_bounds
  simp only [cot_pi_7_9_lower, cot_pi_7_9_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_9_bounds
  simp only [cot_pi_8_9_lower, cot_pi_8_9_upper] at b_cot_8
  rw [cotangentSumVFormula_43_9_lower, cotangentSumVFormula_43_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_943_formula_bound :
  (((99955355099987017877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 43) ∧
  (vasyuninBEntryFormula 9 43 ≤ ((99959858699622513373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_9_43_bounds
  have b_Vkh := cotangentSumVFormula_43_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_9_43_lower, cotangentSumVFormula_9_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_9_lower, cotangentSumVFormula_43_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_43_unfold :
    cotangentSumVFormula 10 43 =
      ((10/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 10 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_10_43_lower : ℚ := -2325251577405525807979 / 439804651110400000000
def cotangentSumVFormula_10_43_upper : ℚ := -2325251568609080442021 / 439804651110400000000
theorem cotangentSumVFormula_10_43_bounds :
  ((cotangentSumVFormula_10_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 43 ∧
  cotangentSumVFormula 10 43 ≤ ((cotangentSumVFormula_10_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_10_43_lower, cotangentSumVFormula_10_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_10_unfold :
    cotangentSumVFormula 43 10 =
      ((3/10 : ℚ) : ℝ) * cotangentTermV 1 10    + 
      ((6/10 : ℚ) : ℝ) * cotangentTermV 2 10    + 
      ((9/10 : ℚ) : ℝ) * cotangentTermV 3 10    + 
      ((2/10 : ℚ) : ℝ) * cotangentTermV 4 10    + 
      ((5/10 : ℚ) : ℝ) * cotangentTermV 5 10    + 
      ((8/10 : ℚ) : ℝ) * cotangentTermV 6 10    + 
      ((1/10 : ℚ) : ℝ) * cotangentTermV 7 10    + 
      ((4/10 : ℚ) : ℝ) * cotangentTermV 8 10    + 
      ((7/10 : ℚ) : ℝ) * cotangentTermV 9 10 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_10]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_43_10_lower : ℚ := -2003802190385119354457 / 3518437208883200000000
def cotangentSumVFormula_43_10_upper : ℚ := -2003802120016316583043 / 3518437208883200000000
theorem cotangentSumVFormula_43_10_bounds :
  ((cotangentSumVFormula_43_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 10 ∧
  cotangentSumVFormula 43 10 ≤ ((cotangentSumVFormula_43_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_10_unfold]
  have b_cot_1 := cot_pi_1_10_bounds
  simp only [cot_pi_1_10_lower, cot_pi_1_10_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_10_bounds
  simp only [cot_pi_2_10_lower, cot_pi_2_10_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_10_bounds
  simp only [cot_pi_3_10_lower, cot_pi_3_10_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_10_bounds
  simp only [cot_pi_4_10_lower, cot_pi_4_10_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_10_bounds
  simp only [cot_pi_5_10_lower, cot_pi_5_10_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_10_bounds
  simp only [cot_pi_6_10_lower, cot_pi_6_10_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_10_bounds
  simp only [cot_pi_7_10_lower, cot_pi_7_10_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_10_bounds
  simp only [cot_pi_8_10_lower, cot_pi_8_10_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_10_bounds
  simp only [cot_pi_9_10_lower, cot_pi_9_10_upper] at b_cot_9
  rw [cotangentSumVFormula_43_10_lower, cotangentSumVFormula_43_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1043_formula_bound :
  (((48542930699579110501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 43) ∧
  (vasyuninBEntryFormula 10 43 ≤ ((48545182499396389499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_10_43_bounds
  have b_Vkh := cotangentSumVFormula_43_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_10_43_lower, cotangentSumVFormula_10_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_10_lower, cotangentSumVFormula_43_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_43_unfold :
    cotangentSumVFormula 11 43 =
      ((11/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 11 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_11_43_lower : ℚ := -1019846168057403424651 / 109951162777600000000
def cotangentSumVFormula_11_43_upper : ℚ := -1019846165858296575349 / 109951162777600000000
theorem cotangentSumVFormula_11_43_bounds :
  ((cotangentSumVFormula_11_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 43 ∧
  cotangentSumVFormula 11 43 ≤ ((cotangentSumVFormula_11_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_43_unfold]
  have b_cot_1 := cot_pi_1_43_bounds
  simp only [cot_pi_1_43_lower, cot_pi_1_43_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_43_bounds
  simp only [cot_pi_2_43_lower, cot_pi_2_43_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_43_bounds
  simp only [cot_pi_3_43_lower, cot_pi_3_43_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_43_bounds
  simp only [cot_pi_4_43_lower, cot_pi_4_43_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_43_bounds
  simp only [cot_pi_5_43_lower, cot_pi_5_43_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_43_bounds
  simp only [cot_pi_6_43_lower, cot_pi_6_43_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_43_bounds
  simp only [cot_pi_7_43_lower, cot_pi_7_43_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_43_bounds
  simp only [cot_pi_8_43_lower, cot_pi_8_43_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_43_bounds
  simp only [cot_pi_9_43_lower, cot_pi_9_43_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_43_bounds
  simp only [cot_pi_10_43_lower, cot_pi_10_43_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_43_bounds
  simp only [cot_pi_11_43_lower, cot_pi_11_43_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_43_bounds
  simp only [cot_pi_12_43_lower, cot_pi_12_43_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_43_bounds
  simp only [cot_pi_13_43_lower, cot_pi_13_43_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_43_bounds
  simp only [cot_pi_14_43_lower, cot_pi_14_43_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_43_bounds
  simp only [cot_pi_15_43_lower, cot_pi_15_43_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_43_bounds
  simp only [cot_pi_16_43_lower, cot_pi_16_43_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_43_bounds
  simp only [cot_pi_17_43_lower, cot_pi_17_43_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_43_bounds
  simp only [cot_pi_18_43_lower, cot_pi_18_43_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_43_bounds
  simp only [cot_pi_19_43_lower, cot_pi_19_43_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_43_bounds
  simp only [cot_pi_20_43_lower, cot_pi_20_43_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_43_bounds
  simp only [cot_pi_21_43_lower, cot_pi_21_43_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_43_bounds
  simp only [cot_pi_22_43_lower, cot_pi_22_43_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_43_bounds
  simp only [cot_pi_23_43_lower, cot_pi_23_43_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_43_bounds
  simp only [cot_pi_24_43_lower, cot_pi_24_43_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_43_bounds
  simp only [cot_pi_25_43_lower, cot_pi_25_43_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_43_bounds
  simp only [cot_pi_26_43_lower, cot_pi_26_43_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_43_bounds
  simp only [cot_pi_27_43_lower, cot_pi_27_43_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_43_bounds
  simp only [cot_pi_28_43_lower, cot_pi_28_43_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_43_bounds
  simp only [cot_pi_29_43_lower, cot_pi_29_43_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_43_bounds
  simp only [cot_pi_30_43_lower, cot_pi_30_43_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_43_bounds
  simp only [cot_pi_31_43_lower, cot_pi_31_43_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_43_bounds
  simp only [cot_pi_32_43_lower, cot_pi_32_43_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_43_bounds
  simp only [cot_pi_33_43_lower, cot_pi_33_43_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_43_bounds
  simp only [cot_pi_34_43_lower, cot_pi_34_43_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_43_bounds
  simp only [cot_pi_35_43_lower, cot_pi_35_43_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_43_bounds
  simp only [cot_pi_36_43_lower, cot_pi_36_43_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_43_bounds
  simp only [cot_pi_37_43_lower, cot_pi_37_43_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_43_bounds
  simp only [cot_pi_38_43_lower, cot_pi_38_43_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_43_bounds
  simp only [cot_pi_39_43_lower, cot_pi_39_43_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_43_bounds
  simp only [cot_pi_40_43_lower, cot_pi_40_43_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_43_bounds
  simp only [cot_pi_41_43_lower, cot_pi_41_43_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_43_bounds
  simp only [cot_pi_42_43_lower, cot_pi_42_43_upper] at b_cot_42
  rw [cotangentSumVFormula_11_43_lower, cotangentSumVFormula_11_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_11_unfold :
    cotangentSumVFormula 43 11 =
      ((10/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_43_11_lower : ℚ := 947374296935982603823 / 219902325555200000000
def cotangentSumVFormula_43_11_upper : ℚ := 947374301334036146177 / 219902325555200000000
theorem cotangentSumVFormula_43_11_bounds :
  ((cotangentSumVFormula_43_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 11 ∧
  cotangentSumVFormula 43 11 ≤ ((cotangentSumVFormula_43_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_11_unfold]
  have b_cot_1 := cot_pi_1_11_bounds
  simp only [cot_pi_1_11_lower, cot_pi_1_11_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_11_bounds
  simp only [cot_pi_2_11_lower, cot_pi_2_11_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_11_bounds
  simp only [cot_pi_3_11_lower, cot_pi_3_11_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_11_bounds
  simp only [cot_pi_4_11_lower, cot_pi_4_11_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_11_bounds
  simp only [cot_pi_5_11_lower, cot_pi_5_11_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_11_bounds
  simp only [cot_pi_6_11_lower, cot_pi_6_11_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_11_bounds
  simp only [cot_pi_7_11_lower, cot_pi_7_11_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_11_bounds
  simp only [cot_pi_8_11_lower, cot_pi_8_11_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_11_bounds
  simp only [cot_pi_9_11_lower, cot_pi_9_11_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_11_bounds
  simp only [cot_pi_10_11_lower, cot_pi_10_11_upper] at b_cot_10
  rw [cotangentSumVFormula_43_11_lower, cotangentSumVFormula_43_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1143_formula_bound :
  (((95342556337992361627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 43) ∧
  (vasyuninBEntryFormula 11 43 ≤ ((95347059937626107123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_11_43_bounds
  have b_Vkh := cotangentSumVFormula_43_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_11_43_lower, cotangentSumVFormula_11_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_11_lower, cotangentSumVFormula_43_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
