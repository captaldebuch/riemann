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

theorem cotangentSumVFormula_25_44_unfold :
    cotangentSumVFormula 25 44 =
      ((25/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 25 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_25_44_lower : ℚ := 3209745827174712742469 / 28147497671065600000000
def cotangentSumVFormula_25_44_upper : ℚ := 3209746390145037257531 / 28147497671065600000000
theorem cotangentSumVFormula_25_44_bounds :
  ((cotangentSumVFormula_25_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 44 ∧
  cotangentSumVFormula 25 44 ≤ ((cotangentSumVFormula_25_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_25_44_lower, cotangentSumVFormula_25_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_25_unfold :
    cotangentSumVFormula 44 25 =
      ((19/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((14/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((21/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((22/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((17/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((11/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((24/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((12/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_44_25_lower : ℚ := 1665702350934622212167 / 879609302220800000000
def cotangentSumVFormula_44_25_upper : ℚ := 104106398032935110763 / 54975581388800000000
theorem cotangentSumVFormula_44_25_bounds :
  ((cotangentSumVFormula_44_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 25 ∧
  cotangentSumVFormula 44 25 ≤ ((cotangentSumVFormula_44_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_25_unfold]
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
  rw [cotangentSumVFormula_44_25_lower, cotangentSumVFormula_44_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2544_formula_bound :
  (((17895422621991875563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 44) ∧
  (vasyuninBEntryFormula 25 44 ≤ ((35793097043799014499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_25_44_bounds
  have b_Vkh := cotangentSumVFormula_44_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_25_44_lower, cotangentSumVFormula_25_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_25_lower, cotangentSumVFormula_44_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_27_44_unfold :
    cotangentSumVFormula 27 44 =
      ((27/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 27 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_27_44_lower : ℚ := 1089914596482295649667 / 879609302220800000000
def cotangentSumVFormula_27_44_upper : ℚ := 1089914614075098100333 / 879609302220800000000
theorem cotangentSumVFormula_27_44_bounds :
  ((cotangentSumVFormula_27_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 27 44 ∧
  cotangentSumVFormula 27 44 ≤ ((cotangentSumVFormula_27_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_27_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_27_44_lower, cotangentSumVFormula_27_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_27_unfold :
    cotangentSumVFormula 44 27 =
      ((17/27 : ℚ) : ℝ) * cotangentTermV 1 27    + 
      ((7/27 : ℚ) : ℝ) * cotangentTermV 2 27    + 
      ((24/27 : ℚ) : ℝ) * cotangentTermV 3 27    + 
      ((14/27 : ℚ) : ℝ) * cotangentTermV 4 27    + 
      ((4/27 : ℚ) : ℝ) * cotangentTermV 5 27    + 
      ((21/27 : ℚ) : ℝ) * cotangentTermV 6 27    + 
      ((11/27 : ℚ) : ℝ) * cotangentTermV 7 27    + 
      ((1/27 : ℚ) : ℝ) * cotangentTermV 8 27    + 
      ((18/27 : ℚ) : ℝ) * cotangentTermV 9 27    + 
      ((8/27 : ℚ) : ℝ) * cotangentTermV 10 27    + 
      ((25/27 : ℚ) : ℝ) * cotangentTermV 11 27    + 
      ((15/27 : ℚ) : ℝ) * cotangentTermV 12 27    + 
      ((5/27 : ℚ) : ℝ) * cotangentTermV 13 27    + 
      ((22/27 : ℚ) : ℝ) * cotangentTermV 14 27    + 
      ((12/27 : ℚ) : ℝ) * cotangentTermV 15 27    + 
      ((2/27 : ℚ) : ℝ) * cotangentTermV 16 27    + 
      ((19/27 : ℚ) : ℝ) * cotangentTermV 17 27    + 
      ((9/27 : ℚ) : ℝ) * cotangentTermV 18 27    + 
      ((26/27 : ℚ) : ℝ) * cotangentTermV 19 27    + 
      ((16/27 : ℚ) : ℝ) * cotangentTermV 20 27    + 
      ((6/27 : ℚ) : ℝ) * cotangentTermV 21 27    + 
      ((23/27 : ℚ) : ℝ) * cotangentTermV 22 27    + 
      ((13/27 : ℚ) : ℝ) * cotangentTermV 23 27    + 
      ((3/27 : ℚ) : ℝ) * cotangentTermV 24 27    + 
      ((20/27 : ℚ) : ℝ) * cotangentTermV 25 27    + 
      ((10/27 : ℚ) : ℝ) * cotangentTermV 26 27 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_27]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((17/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((7/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((24/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((14/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((4/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((21/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((11/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((1/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((18/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((8/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((25/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((15/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((5/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((22/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((12/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((2/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((19/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((9/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((26/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((16/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((6/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((23/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((13/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((3/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((20/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((10/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26]
  try ring

def cotangentSumVFormula_44_27_lower : ℚ := 1213882050515249555917 / 879609302220800000000
def cotangentSumVFormula_44_27_upper : ℚ := 1213882068107636381583 / 879609302220800000000
theorem cotangentSumVFormula_44_27_bounds :
  ((cotangentSumVFormula_44_27_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 27 ∧
  cotangentSumVFormula 44 27 ≤ ((cotangentSumVFormula_44_27_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_27_unfold]
  have b_cot_1 := cot_pi_1_27_bounds
  simp only [cot_pi_1_27_lower, cot_pi_1_27_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_27_bounds
  simp only [cot_pi_2_27_lower, cot_pi_2_27_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_27_bounds
  simp only [cot_pi_3_27_lower, cot_pi_3_27_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_27_bounds
  simp only [cot_pi_4_27_lower, cot_pi_4_27_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_27_bounds
  simp only [cot_pi_5_27_lower, cot_pi_5_27_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_27_bounds
  simp only [cot_pi_6_27_lower, cot_pi_6_27_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_27_bounds
  simp only [cot_pi_7_27_lower, cot_pi_7_27_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_27_bounds
  simp only [cot_pi_8_27_lower, cot_pi_8_27_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_27_bounds
  simp only [cot_pi_9_27_lower, cot_pi_9_27_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_27_bounds
  simp only [cot_pi_10_27_lower, cot_pi_10_27_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_27_bounds
  simp only [cot_pi_11_27_lower, cot_pi_11_27_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_27_bounds
  simp only [cot_pi_12_27_lower, cot_pi_12_27_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_27_bounds
  simp only [cot_pi_13_27_lower, cot_pi_13_27_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_27_bounds
  simp only [cot_pi_14_27_lower, cot_pi_14_27_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_27_bounds
  simp only [cot_pi_15_27_lower, cot_pi_15_27_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_27_bounds
  simp only [cot_pi_16_27_lower, cot_pi_16_27_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_27_bounds
  simp only [cot_pi_17_27_lower, cot_pi_17_27_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_27_bounds
  simp only [cot_pi_18_27_lower, cot_pi_18_27_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_27_bounds
  simp only [cot_pi_19_27_lower, cot_pi_19_27_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_27_bounds
  simp only [cot_pi_20_27_lower, cot_pi_20_27_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_27_bounds
  simp only [cot_pi_21_27_lower, cot_pi_21_27_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_27_bounds
  simp only [cot_pi_22_27_lower, cot_pi_22_27_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_27_bounds
  simp only [cot_pi_23_27_lower, cot_pi_23_27_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_27_bounds
  simp only [cot_pi_24_27_lower, cot_pi_24_27_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_27_bounds
  simp only [cot_pi_25_27_lower, cot_pi_25_27_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_27_bounds
  simp only [cot_pi_26_27_lower, cot_pi_26_27_upper] at b_cot_26
  rw [cotangentSumVFormula_44_27_lower, cotangentSumVFormula_44_27_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2744_formula_bound :
  (((138319643865171020129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 27 44) ∧
  (vasyuninBEntryFormula 27 44 ≤ ((138328651064431729871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 27 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log27 := prim_log_27_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_27_44_bounds
  have b_Vkh := cotangentSumVFormula_44_27_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_27_lower, prim_log_27_upper] at b_log27
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_27_44_lower, cotangentSumVFormula_27_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_27_lower, cotangentSumVFormula_44_27_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_44_unfold :
    cotangentSumVFormula 29 44 =
      ((29/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 29 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_29_44_lower : ℚ := 2108189735126632603823 / 219902325555200000000
def cotangentSumVFormula_29_44_upper : ℚ := 2108189739524825989927 / 219902325555200000000
theorem cotangentSumVFormula_29_44_bounds :
  ((cotangentSumVFormula_29_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 44 ∧
  cotangentSumVFormula 29 44 ≤ ((cotangentSumVFormula_29_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_29_44_lower, cotangentSumVFormula_29_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_29_unfold :
    cotangentSumVFormula 44 29 =
      ((15/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_44_29_lower : ℚ := -2941902764222117995479 / 439804651110400000000
def cotangentSumVFormula_44_29_upper : ℚ := -2941902755425914817021 / 439804651110400000000
theorem cotangentSumVFormula_44_29_bounds :
  ((cotangentSumVFormula_44_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 29 ∧
  cotangentSumVFormula 44 29 ≤ ((cotangentSumVFormula_44_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_29_unfold]
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
  rw [cotangentSumVFormula_44_29_lower, cotangentSumVFormula_44_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2944_formula_bound :
  (((135299531106314332629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 44) ∧
  (vasyuninBEntryFormula 29 44 ≤ ((135308538305574604871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_29_44_bounds
  have b_Vkh := cotangentSumVFormula_44_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_29_44_lower, cotangentSumVFormula_29_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_29_lower, cotangentSumVFormula_44_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_44_unfold :
    cotangentSumVFormula 31 44 =
      ((31/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 31 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_31_44_lower : ℚ := 2737988161335130024667 / 879609302220800000000
def cotangentSumVFormula_31_44_upper : ℚ := 2737988178927893412833 / 879609302220800000000
theorem cotangentSumVFormula_31_44_bounds :
  ((cotangentSumVFormula_31_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 44 ∧
  cotangentSumVFormula 31 44 ≤ ((cotangentSumVFormula_31_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_31_44_lower, cotangentSumVFormula_31_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_31_unfold :
    cotangentSumVFormula 44 31 =
      ((13/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_44_31_lower : ℚ := 1414428490073106212961 / 7036874417766400000000
def cotangentSumVFormula_44_31_upper : ℚ := 1414428630812818787039 / 7036874417766400000000
theorem cotangentSumVFormula_44_31_bounds :
  ((cotangentSumVFormula_44_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 31 ∧
  cotangentSumVFormula 44 31 ≤ ((cotangentSumVFormula_44_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_31_unfold]
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
  rw [cotangentSumVFormula_44_31_lower, cotangentSumVFormula_44_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3144_formula_bound :
  (((131383342540226551379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 44) ∧
  (vasyuninBEntryFormula 31 44 ≤ ((131392349739486761121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_31_44_bounds
  have b_Vkh := cotangentSumVFormula_44_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_31_44_lower, cotangentSumVFormula_31_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_31_lower, cotangentSumVFormula_44_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_35_44_unfold :
    cotangentSumVFormula 35 44 =
      ((35/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 35 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_35_44_lower : ℚ := 575770726996033639237 / 54975581388800000000
def cotangentSumVFormula_35_44_upper : ℚ := 1151541456191151862151 / 109951162777600000000
theorem cotangentSumVFormula_35_44_bounds :
  ((cotangentSumVFormula_35_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 44 ∧
  cotangentSumVFormula 35 44 ≤ ((cotangentSumVFormula_35_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_35_44_lower, cotangentSumVFormula_35_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_35_unfold :
    cotangentSumVFormula 44 35 =
      ((9/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_44_35_lower : ℚ := -3076260669752839089229 / 439804651110400000000
def cotangentSumVFormula_44_35_upper : ℚ := -3076260660956556223271 / 439804651110400000000
theorem cotangentSumVFormula_44_35_bounds :
  ((cotangentSumVFormula_44_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 35 ∧
  cotangentSumVFormula 44 35 ≤ ((cotangentSumVFormula_44_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_35_unfold]
  have b_cot_1 := cot_pi_1_35_bounds
  simp only [cot_pi_1_35_lower, cot_pi_1_35_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_35_bounds
  simp only [cot_pi_2_35_lower, cot_pi_2_35_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_35_bounds
  simp only [cot_pi_3_35_lower, cot_pi_3_35_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_35_bounds
  simp only [cot_pi_4_35_lower, cot_pi_4_35_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_35_bounds
  simp only [cot_pi_5_35_lower, cot_pi_5_35_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_35_bounds
  simp only [cot_pi_6_35_lower, cot_pi_6_35_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_35_bounds
  simp only [cot_pi_7_35_lower, cot_pi_7_35_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_35_bounds
  simp only [cot_pi_8_35_lower, cot_pi_8_35_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_35_bounds
  simp only [cot_pi_9_35_lower, cot_pi_9_35_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_35_bounds
  simp only [cot_pi_10_35_lower, cot_pi_10_35_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_35_bounds
  simp only [cot_pi_11_35_lower, cot_pi_11_35_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_35_bounds
  simp only [cot_pi_12_35_lower, cot_pi_12_35_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_35_bounds
  simp only [cot_pi_13_35_lower, cot_pi_13_35_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_35_bounds
  simp only [cot_pi_14_35_lower, cot_pi_14_35_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_35_bounds
  simp only [cot_pi_15_35_lower, cot_pi_15_35_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_35_bounds
  simp only [cot_pi_16_35_lower, cot_pi_16_35_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_35_bounds
  simp only [cot_pi_17_35_lower, cot_pi_17_35_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_35_bounds
  simp only [cot_pi_18_35_lower, cot_pi_18_35_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_35_bounds
  simp only [cot_pi_19_35_lower, cot_pi_19_35_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_35_bounds
  simp only [cot_pi_20_35_lower, cot_pi_20_35_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_35_bounds
  simp only [cot_pi_21_35_lower, cot_pi_21_35_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_35_bounds
  simp only [cot_pi_22_35_lower, cot_pi_22_35_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_35_bounds
  simp only [cot_pi_23_35_lower, cot_pi_23_35_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_35_bounds
  simp only [cot_pi_24_35_lower, cot_pi_24_35_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_35_bounds
  simp only [cot_pi_25_35_lower, cot_pi_25_35_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_35_bounds
  simp only [cot_pi_26_35_lower, cot_pi_26_35_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_35_bounds
  simp only [cot_pi_27_35_lower, cot_pi_27_35_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_35_bounds
  simp only [cot_pi_28_35_lower, cot_pi_28_35_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_35_bounds
  simp only [cot_pi_29_35_lower, cot_pi_29_35_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_35_bounds
  simp only [cot_pi_30_35_lower, cot_pi_30_35_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_35_bounds
  simp only [cot_pi_31_35_lower, cot_pi_31_35_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_35_bounds
  simp only [cot_pi_32_35_lower, cot_pi_32_35_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_35_bounds
  simp only [cot_pi_33_35_lower, cot_pi_33_35_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_35_bounds
  simp only [cot_pi_34_35_lower, cot_pi_34_35_upper] at b_cot_34
  rw [cotangentSumVFormula_44_35_lower, cotangentSumVFormula_44_35_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3544_formula_bound :
  (((31657252069008610501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 35 44) ∧
  (vasyuninBEntryFormula 35 44 ≤ ((31659503868823514499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 35 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log35 := prim_log_35_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_35_44_bounds
  have b_Vkh := cotangentSumVFormula_44_35_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_35_44_lower, cotangentSumVFormula_35_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_35_lower, cotangentSumVFormula_44_35_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_44_unfold :
    cotangentSumVFormula 37 44 =
      ((37/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 37 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_37_44_lower : ℚ := 2130551873957877916323 / 219902325555200000000
def cotangentSumVFormula_37_44_upper : ℚ := 2130551878356047083677 / 219902325555200000000
theorem cotangentSumVFormula_37_44_bounds :
  ((cotangentSumVFormula_37_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 44 ∧
  cotangentSumVFormula 37 44 ≤ ((cotangentSumVFormula_37_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_37_44_lower, cotangentSumVFormula_37_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_37_unfold :
    cotangentSumVFormula 44 37 =
      ((7/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 44 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_44_37_lower : ℚ := -2796337024865646901729 / 439804651110400000000
def cotangentSumVFormula_44_37_upper : ℚ := -2796337016069371848271 / 439804651110400000000
theorem cotangentSumVFormula_44_37_bounds :
  ((cotangentSumVFormula_44_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 37 ∧
  cotangentSumVFormula 44 37 ≤ ((cotangentSumVFormula_44_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_37_unfold]
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
  rw [cotangentSumVFormula_44_37_lower, cotangentSumVFormula_44_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3744_formula_bound :
  (((125086041336282363879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 44) ∧
  (vasyuninBEntryFormula 37 44 ≤ ((125095048535541636121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_37_44_bounds
  have b_Vkh := cotangentSumVFormula_44_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_37_44_lower, cotangentSumVFormula_37_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_37_lower, cotangentSumVFormula_44_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_39_44_unfold :
    cotangentSumVFormula 39 44 =
      ((39/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 39 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_39_44_lower : ℚ := 1680237010104681731599 / 109951162777600000000
def cotangentSumVFormula_39_44_upper : ℚ := 840118506151881204513 / 54975581388800000000
theorem cotangentSumVFormula_39_44_bounds :
  ((cotangentSumVFormula_39_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 44 ∧
  cotangentSumVFormula 39 44 ≤ ((cotangentSumVFormula_39_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_39_44_lower, cotangentSumVFormula_39_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_39_unfold :
    cotangentSumVFormula 44 39 =
      ((5/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 44 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_44_39_lower : ℚ := -2711145537912431458677 / 219902325555200000000
def cotangentSumVFormula_44_39_upper : ℚ := -2711145533514260728823 / 219902325555200000000
theorem cotangentSumVFormula_44_39_bounds :
  ((cotangentSumVFormula_44_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 39 ∧
  cotangentSumVFormula 44 39 ≤ ((cotangentSumVFormula_44_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_39_unfold]
  have b_cot_1 := cot_pi_1_39_bounds
  simp only [cot_pi_1_39_lower, cot_pi_1_39_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_39_bounds
  simp only [cot_pi_2_39_lower, cot_pi_2_39_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_39_bounds
  simp only [cot_pi_3_39_lower, cot_pi_3_39_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_39_bounds
  simp only [cot_pi_4_39_lower, cot_pi_4_39_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_39_bounds
  simp only [cot_pi_5_39_lower, cot_pi_5_39_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_39_bounds
  simp only [cot_pi_6_39_lower, cot_pi_6_39_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_39_bounds
  simp only [cot_pi_7_39_lower, cot_pi_7_39_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_39_bounds
  simp only [cot_pi_8_39_lower, cot_pi_8_39_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_39_bounds
  simp only [cot_pi_9_39_lower, cot_pi_9_39_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_39_bounds
  simp only [cot_pi_10_39_lower, cot_pi_10_39_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_39_bounds
  simp only [cot_pi_11_39_lower, cot_pi_11_39_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_39_bounds
  simp only [cot_pi_12_39_lower, cot_pi_12_39_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_39_bounds
  simp only [cot_pi_13_39_lower, cot_pi_13_39_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_39_bounds
  simp only [cot_pi_14_39_lower, cot_pi_14_39_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_39_bounds
  simp only [cot_pi_15_39_lower, cot_pi_15_39_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_39_bounds
  simp only [cot_pi_16_39_lower, cot_pi_16_39_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_39_bounds
  simp only [cot_pi_17_39_lower, cot_pi_17_39_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_39_bounds
  simp only [cot_pi_18_39_lower, cot_pi_18_39_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_39_bounds
  simp only [cot_pi_19_39_lower, cot_pi_19_39_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_39_bounds
  simp only [cot_pi_20_39_lower, cot_pi_20_39_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_39_bounds
  simp only [cot_pi_21_39_lower, cot_pi_21_39_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_39_bounds
  simp only [cot_pi_22_39_lower, cot_pi_22_39_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_39_bounds
  simp only [cot_pi_23_39_lower, cot_pi_23_39_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_39_bounds
  simp only [cot_pi_24_39_lower, cot_pi_24_39_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_39_bounds
  simp only [cot_pi_25_39_lower, cot_pi_25_39_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_39_bounds
  simp only [cot_pi_26_39_lower, cot_pi_26_39_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_39_bounds
  simp only [cot_pi_27_39_lower, cot_pi_27_39_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_39_bounds
  simp only [cot_pi_28_39_lower, cot_pi_28_39_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_39_bounds
  simp only [cot_pi_29_39_lower, cot_pi_29_39_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_39_bounds
  simp only [cot_pi_30_39_lower, cot_pi_30_39_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_39_bounds
  simp only [cot_pi_31_39_lower, cot_pi_31_39_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_39_bounds
  simp only [cot_pi_32_39_lower, cot_pi_32_39_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_39_bounds
  simp only [cot_pi_33_39_lower, cot_pi_33_39_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_39_bounds
  simp only [cot_pi_34_39_lower, cot_pi_34_39_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_39_bounds
  simp only [cot_pi_35_39_lower, cot_pi_35_39_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_39_bounds
  simp only [cot_pi_36_39_lower, cot_pi_36_39_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_39_bounds
  simp only [cot_pi_37_39_lower, cot_pi_37_39_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_39_bounds
  simp only [cot_pi_38_39_lower, cot_pi_38_39_upper] at b_cot_38
  rw [cotangentSumVFormula_44_39_lower, cotangentSumVFormula_44_39_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3944_formula_bound :
  (((124336901684327676379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 39 44) ∧
  (vasyuninBEntryFormula 39 44 ≤ ((124345908883587198621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 39 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log39 := prim_log_39_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_39_44_bounds
  have b_Vkh := cotangentSumVFormula_44_39_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_39_44_lower, cotangentSumVFormula_39_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_39_lower, cotangentSumVFormula_44_39_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_44_unfold :
    cotangentSumVFormula 41 44 =
      ((41/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 41 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_41_44_lower : ℚ := 580015269484406077431 / 27487790694400000000
def cotangentSumVFormula_41_44_upper : ℚ := 1160030540068356204513 / 54975581388800000000
theorem cotangentSumVFormula_41_44_bounds :
  ((cotangentSumVFormula_41_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 44 ∧
  cotangentSumVFormula 41 44 ≤ ((cotangentSumVFormula_41_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_41_44_lower, cotangentSumVFormula_41_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_41_unfold :
    cotangentSumVFormula 44 41 =
      ((3/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((6/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((9/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((1/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((4/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((2/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((5/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((8/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 44 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_44_41_lower : ℚ := -1034545505748192923263 / 54975581388800000000
def cotangentSumVFormula_44_41_upper : ℚ := -1034545504648651607987 / 54975581388800000000
theorem cotangentSumVFormula_44_41_bounds :
  ((cotangentSumVFormula_44_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 41 ∧
  cotangentSumVFormula 44 41 ≤ ((cotangentSumVFormula_44_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_41_unfold]
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
  rw [cotangentSumVFormula_44_41_lower, cotangentSumVFormula_44_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4144_formula_bound :
  (((31133843053560516751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 44) ∧
  (vasyuninBEntryFormula 41 44 ≤ ((15568047426687686937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_41_44_bounds
  have b_Vkh := cotangentSumVFormula_44_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_41_44_lower, cotangentSumVFormula_41_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_41_lower, cotangentSumVFormula_44_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_43_44_unfold :
    cotangentSumVFormula 43 44 =
      ((43/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 43 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_43_44_lower : ℚ := 1960644101792651607987 / 54975581388800000000
def cotangentSumVFormula_43_44_upper : ℚ := 1960644102892200735763 / 54975581388800000000
theorem cotangentSumVFormula_43_44_bounds :
  ((cotangentSumVFormula_43_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 44 ∧
  cotangentSumVFormula 43 44 ≤ ((cotangentSumVFormula_43_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_44_unfold]
  have b_cot_1 := cot_pi_1_44_bounds
  simp only [cot_pi_1_44_lower, cot_pi_1_44_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_44_bounds
  simp only [cot_pi_2_44_lower, cot_pi_2_44_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_44_bounds
  simp only [cot_pi_3_44_lower, cot_pi_3_44_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_44_bounds
  simp only [cot_pi_4_44_lower, cot_pi_4_44_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_44_bounds
  simp only [cot_pi_5_44_lower, cot_pi_5_44_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_44_bounds
  simp only [cot_pi_6_44_lower, cot_pi_6_44_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_44_bounds
  simp only [cot_pi_7_44_lower, cot_pi_7_44_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_44_bounds
  simp only [cot_pi_8_44_lower, cot_pi_8_44_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_44_bounds
  simp only [cot_pi_9_44_lower, cot_pi_9_44_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_44_bounds
  simp only [cot_pi_10_44_lower, cot_pi_10_44_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_44_bounds
  simp only [cot_pi_11_44_lower, cot_pi_11_44_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_44_bounds
  simp only [cot_pi_12_44_lower, cot_pi_12_44_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_44_bounds
  simp only [cot_pi_13_44_lower, cot_pi_13_44_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_44_bounds
  simp only [cot_pi_14_44_lower, cot_pi_14_44_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_44_bounds
  simp only [cot_pi_15_44_lower, cot_pi_15_44_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_44_bounds
  simp only [cot_pi_16_44_lower, cot_pi_16_44_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_44_bounds
  simp only [cot_pi_17_44_lower, cot_pi_17_44_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_44_bounds
  simp only [cot_pi_18_44_lower, cot_pi_18_44_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_44_bounds
  simp only [cot_pi_19_44_lower, cot_pi_19_44_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_44_bounds
  simp only [cot_pi_20_44_lower, cot_pi_20_44_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_44_bounds
  simp only [cot_pi_21_44_lower, cot_pi_21_44_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_44_bounds
  simp only [cot_pi_22_44_lower, cot_pi_22_44_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_44_bounds
  simp only [cot_pi_23_44_lower, cot_pi_23_44_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_44_bounds
  simp only [cot_pi_24_44_lower, cot_pi_24_44_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_44_bounds
  simp only [cot_pi_25_44_lower, cot_pi_25_44_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_44_bounds
  simp only [cot_pi_26_44_lower, cot_pi_26_44_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_44_bounds
  simp only [cot_pi_27_44_lower, cot_pi_27_44_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_44_bounds
  simp only [cot_pi_28_44_lower, cot_pi_28_44_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_44_bounds
  simp only [cot_pi_29_44_lower, cot_pi_29_44_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_44_bounds
  simp only [cot_pi_30_44_lower, cot_pi_30_44_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_44_bounds
  simp only [cot_pi_31_44_lower, cot_pi_31_44_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_44_bounds
  simp only [cot_pi_32_44_lower, cot_pi_32_44_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_44_bounds
  simp only [cot_pi_33_44_lower, cot_pi_33_44_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_44_bounds
  simp only [cot_pi_34_44_lower, cot_pi_34_44_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_44_bounds
  simp only [cot_pi_35_44_lower, cot_pi_35_44_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_44_bounds
  simp only [cot_pi_36_44_lower, cot_pi_36_44_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_44_bounds
  simp only [cot_pi_37_44_lower, cot_pi_37_44_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_44_bounds
  simp only [cot_pi_38_44_lower, cot_pi_38_44_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_44_bounds
  simp only [cot_pi_39_44_lower, cot_pi_39_44_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_44_bounds
  simp only [cot_pi_40_44_lower, cot_pi_40_44_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_44_bounds
  simp only [cot_pi_41_44_lower, cot_pi_41_44_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_44_bounds
  simp only [cot_pi_42_44_lower, cot_pi_42_44_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_44_bounds
  simp only [cot_pi_43_44_lower, cot_pi_43_44_upper] at b_cot_43
  rw [cotangentSumVFormula_43_44_lower, cotangentSumVFormula_43_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_43_unfold :
    cotangentSumVFormula 44 43 =
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
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 44 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_44_43_lower : ℚ := -1899187841898131204513 / 54975581388800000000
def cotangentSumVFormula_44_43_upper : ℚ := -1899187840798574264237 / 54975581388800000000
theorem cotangentSumVFormula_44_43_bounds :
  ((cotangentSumVFormula_44_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 43 ∧
  cotangentSumVFormula 44 43 ≤ ((cotangentSumVFormula_44_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_43_unfold]
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
  rw [cotangentSumVFormula_44_43_lower, cotangentSumVFormula_44_43_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4344_formula_bound :
  (((31580788932869141751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 43 44) ∧
  (vasyuninBEntryFormula 43 44 ≤ ((15791520366342155687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 43 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log43 := log_43_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_43_44_bounds
  have b_Vkh := cotangentSumVFormula_44_43_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_43_44_lower, cotangentSumVFormula_43_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_43_lower, cotangentSumVFormula_44_43_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_45_unfold :
    cotangentSumVFormula 1 45 =
      ((1/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 1 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_1_45_lower : ℚ := -2022498221511643704513 / 54975581388800000000
def cotangentSumVFormula_1_45_upper : ℚ := -2022498220412081295487 / 54975581388800000000
theorem cotangentSumVFormula_1_45_bounds :
  ((cotangentSumVFormula_1_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 45 ∧
  cotangentSumVFormula 1 45 ≤ ((cotangentSumVFormula_1_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_1_45_lower, cotangentSumVFormula_1_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_1_unfold :
    cotangentSumVFormula 45 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_45_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_45_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_45_1_bounds :
  ((cotangentSumVFormula_45_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 1 ∧
  cotangentSumVFormula 45 1 ≤ ((cotangentSumVFormula_45_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_1_unfold]
  rw [cotangentSumVFormula_45_1_lower, cotangentSumVFormula_45_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_145_formula_bound :
  (((37988651248010969313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 45) ∧
  (vasyuninBEntryFormula 1 45 ≤ ((37989777147938280687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_1_45_bounds
  have b_Vkh := cotangentSumVFormula_45_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_1_45_lower, cotangentSumVFormula_1_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_1_lower, cotangentSumVFormula_45_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_45_unfold :
    cotangentSumVFormula 2 45 =
      ((2/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 2 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_2_45_lower : ℚ := -2988013905592582330901 / 109951162777600000000
def cotangentSumVFormula_2_45_upper : ℚ := -2988013903393457512849 / 109951162777600000000
theorem cotangentSumVFormula_2_45_bounds :
  ((cotangentSumVFormula_2_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 45 ∧
  cotangentSumVFormula 2 45 ≤ ((cotangentSumVFormula_2_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_2_45_lower, cotangentSumVFormula_2_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_2_unfold :
    cotangentSumVFormula 45 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_45_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_45_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_45_2_bounds :
  ((cotangentSumVFormula_45_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 2 ∧
  cotangentSumVFormula 45 2 ≤ ((cotangentSumVFormula_45_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_45_2_lower, cotangentSumVFormula_45_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_245_formula_bound :
  (((67210780367361204251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 45) ∧
  (vasyuninBEntryFormula 2 45 ≤ ((67213032167195045749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_2_45_bounds
  have b_Vkh := cotangentSumVFormula_45_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_2_45_lower, cotangentSumVFormula_2_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_2_lower, cotangentSumVFormula_45_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_45_unfold :
    cotangentSumVFormula 4 45 =
      ((4/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 4 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_4_45_lower : ℚ := -1911087737409046393401 / 109951162777600000000
def cotangentSumVFormula_4_45_upper : ℚ := -1911087735209925481599 / 109951162777600000000
theorem cotangentSumVFormula_4_45_bounds :
  ((cotangentSumVFormula_4_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 45 ∧
  cotangentSumVFormula 4 45 ≤ ((cotangentSumVFormula_4_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_4_45_lower, cotangentSumVFormula_4_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_4_unfold :
    cotangentSumVFormula 45 4 =
      ((1/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((3/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_45_4_lower : ℚ := -1759218639625974041957 / 3518437208883200000000
def cotangentSumVFormula_45_4_upper : ℚ := -1759218569257223614293 / 3518437208883200000000
theorem cotangentSumVFormula_45_4_bounds :
  ((cotangentSumVFormula_45_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 4 ∧
  cotangentSumVFormula 45 4 ≤ ((cotangentSumVFormula_45_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_45_4_lower, cotangentSumVFormula_45_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_445_formula_bound :
  (((58523442071545235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 45) ∧
  (vasyuninBEntryFormula 4 45 ≤ ((58525693871368576999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_4_45_bounds
  have b_Vkh := cotangentSumVFormula_45_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_4_45_lower, cotangentSumVFormula_4_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_4_lower, cotangentSumVFormula_45_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_45_unfold :
    cotangentSumVFormula 7 45 =
      ((7/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 7 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_7_45_lower : ℚ := -1206692529727065143401 / 109951162777600000000
def cotangentSumVFormula_7_45_upper : ℚ := -1206692527527943450349 / 109951162777600000000
theorem cotangentSumVFormula_7_45_bounds :
  ((cotangentSumVFormula_7_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 45 ∧
  cotangentSumVFormula 7 45 ≤ ((cotangentSumVFormula_7_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_7_45_lower, cotangentSumVFormula_7_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_7_unfold :
    cotangentSumVFormula 45 7 =
      ((3/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_45_7_lower : ℚ := 154071743954285493417 / 879609302220800000000
def cotangentSumVFormula_45_7_upper : ℚ := 154071761546478569083 / 879609302220800000000
theorem cotangentSumVFormula_45_7_bounds :
  ((cotangentSumVFormula_45_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 7 ∧
  cotangentSumVFormula 45 7 ≤ ((cotangentSumVFormula_45_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_7_unfold]
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
  rw [cotangentSumVFormula_45_7_lower, cotangentSumVFormula_45_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_745_formula_bound :
  (((51421922370316423001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 45) ∧
  (vasyuninBEntryFormula 7 45 ≤ ((51424174170135576999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_7_45_bounds
  have b_Vkh := cotangentSumVFormula_45_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_7_45_lower, cotangentSumVFormula_7_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_7_lower, cotangentSumVFormula_45_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_45_unfold :
    cotangentSumVFormula 8 45 =
      ((8/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 8 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_8_45_lower : ℚ := -2113488713117587708677 / 219902325555200000000
def cotangentSumVFormula_8_45_upper : ℚ := -2113488708719343541323 / 219902325555200000000
theorem cotangentSumVFormula_8_45_bounds :
  ((cotangentSumVFormula_8_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 45 ∧
  cotangentSumVFormula 8 45 ≤ ((cotangentSumVFormula_8_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_8_45_lower, cotangentSumVFormula_8_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_8_unfold :
    cotangentSumVFormula 45 8 =
      ((5/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_45_8_lower : ℚ := 728692187546585439959 / 1759218604441600000000
def cotangentSumVFormula_45_8_upper : ℚ := 728692222730973935041 / 1759218604441600000000
theorem cotangentSumVFormula_45_8_bounds :
  ((cotangentSumVFormula_45_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 8 ∧
  cotangentSumVFormula 45 8 ≤ ((cotangentSumVFormula_45_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_8_unfold]
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
  rw [cotangentSumVFormula_45_8_lower, cotangentSumVFormula_45_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_845_formula_bound :
  (((99453936594926236627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 45) ∧
  (vasyuninBEntryFormula 8 45 ≤ ((99458440194563169623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_8_45_bounds
  have b_Vkh := cotangentSumVFormula_45_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_8_45_lower, cotangentSumVFormula_8_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_8_lower, cotangentSumVFormula_45_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_45_unfold :
    cotangentSumVFormula 11 45 =
      ((11/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 11 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_11_45_lower : ℚ := -38064425411019703819 / 27487790694400000000
def cotangentSumVFormula_11_45_upper : ℚ := -152257699444961419099 / 109951162777600000000
theorem cotangentSumVFormula_11_45_bounds :
  ((cotangentSumVFormula_11_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 45 ∧
  cotangentSumVFormula 11 45 ≤ ((cotangentSumVFormula_11_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_11_45_lower, cotangentSumVFormula_11_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_11_unfold :
    cotangentSumVFormula 45 11 =
      ((1/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_45_11_lower : ℚ := -947374301334035364927 / 219902325555200000000
def cotangentSumVFormula_45_11_upper : ℚ := -947374296935981041323 / 219902325555200000000
theorem cotangentSumVFormula_45_11_bounds :
  ((cotangentSumVFormula_45_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 11 ∧
  cotangentSumVFormula 45 11 ≤ ((cotangentSumVFormula_45_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_11_unfold]
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
  rw [cotangentSumVFormula_45_11_lower, cotangentSumVFormula_45_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1145_formula_bound :
  (((46153760881828079251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 45) ∧
  (vasyuninBEntryFormula 11 45 ≤ ((23078006340822593187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_11_45_bounds
  have b_Vkh := cotangentSumVFormula_45_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_11_45_lower, cotangentSumVFormula_11_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_11_lower, cotangentSumVFormula_45_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_45_unfold :
    cotangentSumVFormula 13 45 =
      ((13/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 13 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_13_45_lower : ℚ := -2299112716994261745479 / 439804651110400000000
def cotangentSumVFormula_13_45_upper : ℚ := -2299112708197799973271 / 439804651110400000000
theorem cotangentSumVFormula_13_45_bounds :
  ((cotangentSumVFormula_13_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 45 ∧
  cotangentSumVFormula 13 45 ≤ ((cotangentSumVFormula_13_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_13_45_lower, cotangentSumVFormula_13_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_13_unfold :
    cotangentSumVFormula 45 13 =
      ((6/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_45_13_lower : ℚ := 2528030260896387783709 / 1759218604441600000000
def cotangentSumVFormula_45_13_upper : ℚ := 2528030296080838778791 / 1759218604441600000000
theorem cotangentSumVFormula_45_13_bounds :
  ((cotangentSumVFormula_45_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 13 ∧
  cotangentSumVFormula 45 13 ≤ ((cotangentSumVFormula_45_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_13_unfold]
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
  rw [cotangentSumVFormula_45_13_lower, cotangentSumVFormula_45_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1345_formula_bound :
  (((87167288120372517877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 45) ∧
  (vasyuninBEntryFormula 13 45 ≤ ((87171791720005638373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_13_45_bounds
  have b_Vkh := cotangentSumVFormula_45_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_13_45_lower, cotangentSumVFormula_13_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_13_lower, cotangentSumVFormula_45_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_14_45_unfold :
    cotangentSumVFormula 14 45 =
      ((14/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 14 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_14_45_lower : ℚ := -2537362376708045916957 / 3518437208883200000000
def cotangentSumVFormula_14_45_upper : ℚ := -2537362306336416583043 / 3518437208883200000000
theorem cotangentSumVFormula_14_45_bounds :
  ((cotangentSumVFormula_14_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 45 ∧
  cotangentSumVFormula 14 45 ≤ ((cotangentSumVFormula_14_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_14_45_lower, cotangentSumVFormula_14_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_14_unfold :
    cotangentSumVFormula 45 14 =
      ((3/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((1/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_45_14_lower : ℚ := -1048026653573911745479 / 439804651110400000000
def cotangentSumVFormula_45_14_upper : ℚ := -1048026644777790598271 / 439804651110400000000
theorem cotangentSumVFormula_45_14_bounds :
  ((cotangentSumVFormula_45_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 14 ∧
  cotangentSumVFormula 45 14 ≤ ((cotangentSumVFormula_45_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_14_unfold]
  have b_cot_1 := cot_pi_1_14_bounds
  simp only [cot_pi_1_14_lower, cot_pi_1_14_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_14_bounds
  simp only [cot_pi_2_14_lower, cot_pi_2_14_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_14_bounds
  simp only [cot_pi_3_14_lower, cot_pi_3_14_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_14_bounds
  simp only [cot_pi_4_14_lower, cot_pi_4_14_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_14_bounds
  simp only [cot_pi_5_14_lower, cot_pi_5_14_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_14_bounds
  simp only [cot_pi_6_14_lower, cot_pi_6_14_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_14_bounds
  simp only [cot_pi_7_14_lower, cot_pi_7_14_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_14_bounds
  simp only [cot_pi_8_14_lower, cot_pi_8_14_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_14_bounds
  simp only [cot_pi_9_14_lower, cot_pi_9_14_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_14_bounds
  simp only [cot_pi_10_14_lower, cot_pi_10_14_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_14_bounds
  simp only [cot_pi_11_14_lower, cot_pi_11_14_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_14_bounds
  simp only [cot_pi_12_14_lower, cot_pi_12_14_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_14_bounds
  simp only [cot_pi_13_14_lower, cot_pi_13_14_upper] at b_cot_13
  rw [cotangentSumVFormula_45_14_lower, cotangentSumVFormula_45_14_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1445_formula_bound :
  (((2677017786674556711 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 14 45) ∧
  (vasyuninBEntryFormula 14 45 ≤ ((42834536386609233249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 14 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log14 := prim_log_14_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_14_45_bounds
  have b_Vkh := cotangentSumVFormula_45_14_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_14_45_lower, cotangentSumVFormula_14_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_14_lower, cotangentSumVFormula_45_14_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_16_45_unfold :
    cotangentSumVFormula 16 45 =
      ((16/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 16 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_16_45_lower : ℚ := -2053485141662314089229 / 439804651110400000000
def cotangentSumVFormula_16_45_upper : ℚ := -2053485132865859348271 / 439804651110400000000
theorem cotangentSumVFormula_16_45_bounds :
  ((cotangentSumVFormula_16_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 45 ∧
  cotangentSumVFormula 16 45 ≤ ((cotangentSumVFormula_16_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_16_45_lower, cotangentSumVFormula_16_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_16_unfold :
    cotangentSumVFormula 45 16 =
      ((13/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_45_16_lower : ℚ := 2514944475109533930917 / 879609302220800000000
def cotangentSumVFormula_45_16_upper : ℚ := 2514944492701760600333 / 879609302220800000000
theorem cotangentSumVFormula_45_16_bounds :
  ((cotangentSumVFormula_45_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 16 ∧
  cotangentSumVFormula 45 16 ≤ ((cotangentSumVFormula_45_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_16_unfold]
  have b_cot_1 := cot_pi_1_16_bounds
  simp only [cot_pi_1_16_lower, cot_pi_1_16_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_16_bounds
  simp only [cot_pi_2_16_lower, cot_pi_2_16_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_16_bounds
  simp only [cot_pi_3_16_lower, cot_pi_3_16_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_16_bounds
  simp only [cot_pi_4_16_lower, cot_pi_4_16_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_16_bounds
  simp only [cot_pi_5_16_lower, cot_pi_5_16_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_16_bounds
  simp only [cot_pi_6_16_lower, cot_pi_6_16_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_16_bounds
  simp only [cot_pi_7_16_lower, cot_pi_7_16_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_16_bounds
  simp only [cot_pi_8_16_lower, cot_pi_8_16_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_16_bounds
  simp only [cot_pi_9_16_lower, cot_pi_9_16_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_16_bounds
  simp only [cot_pi_10_16_lower, cot_pi_10_16_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_16_bounds
  simp only [cot_pi_11_16_lower, cot_pi_11_16_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_16_bounds
  simp only [cot_pi_12_16_lower, cot_pi_12_16_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_16_bounds
  simp only [cot_pi_13_16_lower, cot_pi_13_16_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_16_bounds
  simp only [cot_pi_14_16_lower, cot_pi_14_16_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_16_bounds
  simp only [cot_pi_15_16_lower, cot_pi_15_16_upper] at b_cot_15
  rw [cotangentSumVFormula_45_16_lower, cotangentSumVFormula_45_16_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1645_formula_bound :
  (((82248254011583799127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 16 45) ∧
  (vasyuninBEntryFormula 16 45 ≤ ((82252757611215763373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 16 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log16 := prim_log_16_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_16_45_bounds
  have b_Vkh := cotangentSumVFormula_45_16_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_16_45_lower, cotangentSumVFormula_16_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_16_lower, cotangentSumVFormula_45_16_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_45_unfold :
    cotangentSumVFormula 17 45 =
      ((17/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 17 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_17_45_lower : ℚ := -1416432179122100807979 / 439804651110400000000
def cotangentSumVFormula_17_45_upper : ℚ := -1416432170325655442021 / 439804651110400000000
theorem cotangentSumVFormula_17_45_bounds :
  ((cotangentSumVFormula_17_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 45 ∧
  cotangentSumVFormula 17 45 ≤ ((cotangentSumVFormula_17_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_17_45_lower, cotangentSumVFormula_17_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_17_unfold :
    cotangentSumVFormula 45 17 =
      ((11/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_45_17_lower : ℚ := 909029653276409348271 / 439804651110400000000
def cotangentSumVFormula_45_17_upper : ℚ := 909029662072535182979 / 439804651110400000000
theorem cotangentSumVFormula_45_17_bounds :
  ((cotangentSumVFormula_45_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 17 ∧
  cotangentSumVFormula 45 17 ≤ ((cotangentSumVFormula_45_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_17_unfold]
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
  rw [cotangentSumVFormula_45_17_lower, cotangentSumVFormula_45_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1745_formula_bound :
  (((626964302032908709 / 17592186044416000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 45) ∧
  (vasyuninBEntryFormula 17 45 ≤ ((40127967129922014499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_17_45_bounds
  have b_Vkh := cotangentSumVFormula_45_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_17_45_lower, cotangentSumVFormula_17_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_17_lower, cotangentSumVFormula_45_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_45_unfold :
    cotangentSumVFormula 19 45 =
      ((19/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 19 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_19_45_lower : ℚ := 1794425358231027627459 / 1759218604441600000000
def cotangentSumVFormula_19_45_upper : ℚ := 1794425393416753622541 / 1759218604441600000000
theorem cotangentSumVFormula_19_45_bounds :
  ((cotangentSumVFormula_19_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 45 ∧
  cotangentSumVFormula 19 45 ≤ ((cotangentSumVFormula_19_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_19_45_lower, cotangentSumVFormula_19_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_19_unfold :
    cotangentSumVFormula 45 19 =
      ((7/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_45_19_lower : ℚ := -132682529281465143401 / 109951162777600000000
def cotangentSumVFormula_45_19_upper : ℚ := -530730108329723410771 / 439804651110400000000
theorem cotangentSumVFormula_45_19_bounds :
  ((cotangentSumVFormula_45_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 19 ∧
  cotangentSumVFormula 45 19 ≤ ((cotangentSumVFormula_45_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_19_unfold]
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
  rw [cotangentSumVFormula_45_19_lower, cotangentSumVFormula_45_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1945_formula_bound :
  (((77495402468692236627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 45) ∧
  (vasyuninBEntryFormula 19 45 ≤ ((77499906068323482123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_19_45_bounds
  have b_Vkh := cotangentSumVFormula_45_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_19_45_lower, cotangentSumVFormula_19_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_19_lower, cotangentSumVFormula_45_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_22_45_unfold :
    cotangentSumVFormula 22 45 =
      ((22/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 22 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_22_45_lower : ℚ := 1476987335211398137849 / 109951162777600000000
def cotangentSumVFormula_22_45_upper : ℚ := 738493668705249954513 / 54975581388800000000
theorem cotangentSumVFormula_22_45_bounds :
  ((cotangentSumVFormula_22_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 22 45 ∧
  cotangentSumVFormula 22 45 ≤ ((cotangentSumVFormula_22_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_22_45_unfold]
  have b_cot_1 := cot_pi_1_45_bounds
  simp only [cot_pi_1_45_lower, cot_pi_1_45_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_45_bounds
  simp only [cot_pi_2_45_lower, cot_pi_2_45_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_45_bounds
  simp only [cot_pi_3_45_lower, cot_pi_3_45_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_45_bounds
  simp only [cot_pi_4_45_lower, cot_pi_4_45_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_45_bounds
  simp only [cot_pi_5_45_lower, cot_pi_5_45_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_45_bounds
  simp only [cot_pi_6_45_lower, cot_pi_6_45_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_45_bounds
  simp only [cot_pi_7_45_lower, cot_pi_7_45_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_45_bounds
  simp only [cot_pi_8_45_lower, cot_pi_8_45_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_45_bounds
  simp only [cot_pi_9_45_lower, cot_pi_9_45_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_45_bounds
  simp only [cot_pi_10_45_lower, cot_pi_10_45_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_45_bounds
  simp only [cot_pi_11_45_lower, cot_pi_11_45_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_45_bounds
  simp only [cot_pi_12_45_lower, cot_pi_12_45_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_45_bounds
  simp only [cot_pi_13_45_lower, cot_pi_13_45_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_45_bounds
  simp only [cot_pi_14_45_lower, cot_pi_14_45_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_45_bounds
  simp only [cot_pi_15_45_lower, cot_pi_15_45_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_45_bounds
  simp only [cot_pi_16_45_lower, cot_pi_16_45_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_45_bounds
  simp only [cot_pi_17_45_lower, cot_pi_17_45_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_45_bounds
  simp only [cot_pi_18_45_lower, cot_pi_18_45_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_45_bounds
  simp only [cot_pi_19_45_lower, cot_pi_19_45_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_45_bounds
  simp only [cot_pi_20_45_lower, cot_pi_20_45_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_45_bounds
  simp only [cot_pi_21_45_lower, cot_pi_21_45_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_45_bounds
  simp only [cot_pi_22_45_lower, cot_pi_22_45_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_45_bounds
  simp only [cot_pi_23_45_lower, cot_pi_23_45_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_45_bounds
  simp only [cot_pi_24_45_lower, cot_pi_24_45_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_45_bounds
  simp only [cot_pi_25_45_lower, cot_pi_25_45_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_45_bounds
  simp only [cot_pi_26_45_lower, cot_pi_26_45_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_45_bounds
  simp only [cot_pi_27_45_lower, cot_pi_27_45_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_45_bounds
  simp only [cot_pi_28_45_lower, cot_pi_28_45_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_45_bounds
  simp only [cot_pi_29_45_lower, cot_pi_29_45_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_45_bounds
  simp only [cot_pi_30_45_lower, cot_pi_30_45_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_45_bounds
  simp only [cot_pi_31_45_lower, cot_pi_31_45_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_45_bounds
  simp only [cot_pi_32_45_lower, cot_pi_32_45_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_45_bounds
  simp only [cot_pi_33_45_lower, cot_pi_33_45_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_45_bounds
  simp only [cot_pi_34_45_lower, cot_pi_34_45_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_45_bounds
  simp only [cot_pi_35_45_lower, cot_pi_35_45_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_45_bounds
  simp only [cot_pi_36_45_lower, cot_pi_36_45_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_45_bounds
  simp only [cot_pi_37_45_lower, cot_pi_37_45_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_45_bounds
  simp only [cot_pi_38_45_lower, cot_pi_38_45_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_45_bounds
  simp only [cot_pi_39_45_lower, cot_pi_39_45_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_45_bounds
  simp only [cot_pi_40_45_lower, cot_pi_40_45_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_45_bounds
  simp only [cot_pi_41_45_lower, cot_pi_41_45_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_45_bounds
  simp only [cot_pi_42_45_lower, cot_pi_42_45_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_45_bounds
  simp only [cot_pi_43_45_lower, cot_pi_43_45_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_45_bounds
  simp only [cot_pi_44_45_lower, cot_pi_44_45_upper] at b_cot_44
  rw [cotangentSumVFormula_22_45_lower, cotangentSumVFormula_22_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_22_unfold :
    cotangentSumVFormula 45 22 =
      ((1/22 : ℚ) : ℝ) * cotangentTermV 1 22    + 
      ((2/22 : ℚ) : ℝ) * cotangentTermV 2 22    + 
      ((3/22 : ℚ) : ℝ) * cotangentTermV 3 22    + 
      ((4/22 : ℚ) : ℝ) * cotangentTermV 4 22    + 
      ((5/22 : ℚ) : ℝ) * cotangentTermV 5 22    + 
      ((6/22 : ℚ) : ℝ) * cotangentTermV 6 22    + 
      ((7/22 : ℚ) : ℝ) * cotangentTermV 7 22    + 
      ((8/22 : ℚ) : ℝ) * cotangentTermV 8 22    + 
      ((9/22 : ℚ) : ℝ) * cotangentTermV 9 22    + 
      ((10/22 : ℚ) : ℝ) * cotangentTermV 10 22    + 
      ((11/22 : ℚ) : ℝ) * cotangentTermV 11 22    + 
      ((12/22 : ℚ) : ℝ) * cotangentTermV 12 22    + 
      ((13/22 : ℚ) : ℝ) * cotangentTermV 13 22    + 
      ((14/22 : ℚ) : ℝ) * cotangentTermV 14 22    + 
      ((15/22 : ℚ) : ℝ) * cotangentTermV 15 22    + 
      ((16/22 : ℚ) : ℝ) * cotangentTermV 16 22    + 
      ((17/22 : ℚ) : ℝ) * cotangentTermV 17 22    + 
      ((18/22 : ℚ) : ℝ) * cotangentTermV 18 22    + 
      ((19/22 : ℚ) : ℝ) * cotangentTermV 19 22    + 
      ((20/22 : ℚ) : ℝ) * cotangentTermV 20 22    + 
      ((21/22 : ℚ) : ℝ) * cotangentTermV 21 22 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_22]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((1/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((2/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((3/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((4/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((5/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((6/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((7/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((8/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((9/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((10/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((11/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((12/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((13/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((14/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((15/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((16/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((17/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((18/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((19/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((20/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((21/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21]
  try ring

def cotangentSumVFormula_45_22_lower : ℚ := -2889538651195121302427 / 219902325555200000000
def cotangentSumVFormula_45_22_upper : ℚ := -2889538646797031041323 / 219902325555200000000
theorem cotangentSumVFormula_45_22_bounds :
  ((cotangentSumVFormula_45_22_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 22 ∧
  cotangentSumVFormula 45 22 ≤ ((cotangentSumVFormula_45_22_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_22_unfold]
  have b_cot_1 := cot_pi_1_22_bounds
  simp only [cot_pi_1_22_lower, cot_pi_1_22_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_22_bounds
  simp only [cot_pi_2_22_lower, cot_pi_2_22_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_22_bounds
  simp only [cot_pi_3_22_lower, cot_pi_3_22_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_22_bounds
  simp only [cot_pi_4_22_lower, cot_pi_4_22_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_22_bounds
  simp only [cot_pi_5_22_lower, cot_pi_5_22_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_22_bounds
  simp only [cot_pi_6_22_lower, cot_pi_6_22_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_22_bounds
  simp only [cot_pi_7_22_lower, cot_pi_7_22_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_22_bounds
  simp only [cot_pi_8_22_lower, cot_pi_8_22_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_22_bounds
  simp only [cot_pi_9_22_lower, cot_pi_9_22_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_22_bounds
  simp only [cot_pi_10_22_lower, cot_pi_10_22_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_22_bounds
  simp only [cot_pi_11_22_lower, cot_pi_11_22_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_22_bounds
  simp only [cot_pi_12_22_lower, cot_pi_12_22_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_22_bounds
  simp only [cot_pi_13_22_lower, cot_pi_13_22_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_22_bounds
  simp only [cot_pi_14_22_lower, cot_pi_14_22_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_22_bounds
  simp only [cot_pi_15_22_lower, cot_pi_15_22_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_22_bounds
  simp only [cot_pi_16_22_lower, cot_pi_16_22_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_22_bounds
  simp only [cot_pi_17_22_lower, cot_pi_17_22_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_22_bounds
  simp only [cot_pi_18_22_lower, cot_pi_18_22_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_22_bounds
  simp only [cot_pi_19_22_lower, cot_pi_19_22_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_22_bounds
  simp only [cot_pi_20_22_lower, cot_pi_20_22_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_22_bounds
  simp only [cot_pi_21_22_lower, cot_pi_21_22_upper] at b_cot_21
  rw [cotangentSumVFormula_45_22_lower, cotangentSumVFormula_45_22_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2245_formula_bound :
  (((9536389283636023719 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 22 45) ∧
  (vasyuninBEntryFormula 22 45 ≤ ((9536952233589882531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 22 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log22 := prim_log_22_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_22_45_bounds
  have b_Vkh := cotangentSumVFormula_45_22_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_22_lower, prim_log_22_upper] at b_log22
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_22_45_lower, cotangentSumVFormula_22_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_22_lower, cotangentSumVFormula_45_22_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
