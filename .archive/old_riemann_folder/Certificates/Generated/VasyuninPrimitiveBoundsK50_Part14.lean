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

theorem cotangentSumVFormula_23_50_unfold :
    cotangentSumVFormula 23 50 =
      ((23/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 23 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_23_50_lower : ℚ := 624507645065780169099 / 109951162777600000000
def cotangentSumVFormula_23_50_upper : ℚ := 312253823632449954513 / 54975581388800000000
theorem cotangentSumVFormula_23_50_bounds :
  ((cotangentSumVFormula_23_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 50 ∧
  cotangentSumVFormula 23 50 ≤ ((cotangentSumVFormula_23_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_23_50_lower, cotangentSumVFormula_23_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_23_unfold :
    cotangentSumVFormula 50 23 =
      ((4/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_50_23_lower : ℚ := -73408348103611219097 / 13743895347200000000
def cotangentSumVFormula_50_23_upper : ℚ := -1174533565259685728823 / 219902325555200000000
theorem cotangentSumVFormula_50_23_bounds :
  ((cotangentSumVFormula_50_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 23 ∧
  cotangentSumVFormula 50 23 ≤ ((cotangentSumVFormula_50_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_23_unfold]
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
  rw [cotangentSumVFormula_50_23_lower, cotangentSumVFormula_50_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2350_formula_bound :
  (((68528765291625549127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 50) ∧
  (vasyuninBEntryFormula 23 50 ≤ ((34266634445628264499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_23_50_bounds
  have b_Vkh := cotangentSumVFormula_50_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_23_50_lower, cotangentSumVFormula_23_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_23_lower, cotangentSumVFormula_50_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_27_50_unfold :
    cotangentSumVFormula 27 50 =
      ((27/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 27 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_27_50_lower : ℚ := -1249015294529772864927 / 219902325555200000000
def cotangentSumVFormula_27_50_upper : ℚ := -1249015290131536510073 / 219902325555200000000
theorem cotangentSumVFormula_27_50_bounds :
  ((cotangentSumVFormula_27_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 27 50 ∧
  cotangentSumVFormula 27 50 ≤ ((cotangentSumVFormula_27_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_27_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_27_50_lower, cotangentSumVFormula_27_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_27_unfold :
    cotangentSumVFormula 50 27 =
      ((23/27 : ℚ) : ℝ) * cotangentTermV 1 27    + 
      ((19/27 : ℚ) : ℝ) * cotangentTermV 2 27    + 
      ((15/27 : ℚ) : ℝ) * cotangentTermV 3 27    + 
      ((11/27 : ℚ) : ℝ) * cotangentTermV 4 27    + 
      ((7/27 : ℚ) : ℝ) * cotangentTermV 5 27    + 
      ((3/27 : ℚ) : ℝ) * cotangentTermV 6 27    + 
      ((26/27 : ℚ) : ℝ) * cotangentTermV 7 27    + 
      ((22/27 : ℚ) : ℝ) * cotangentTermV 8 27    + 
      ((18/27 : ℚ) : ℝ) * cotangentTermV 9 27    + 
      ((14/27 : ℚ) : ℝ) * cotangentTermV 10 27    + 
      ((10/27 : ℚ) : ℝ) * cotangentTermV 11 27    + 
      ((6/27 : ℚ) : ℝ) * cotangentTermV 12 27    + 
      ((2/27 : ℚ) : ℝ) * cotangentTermV 13 27    + 
      ((25/27 : ℚ) : ℝ) * cotangentTermV 14 27    + 
      ((21/27 : ℚ) : ℝ) * cotangentTermV 15 27    + 
      ((17/27 : ℚ) : ℝ) * cotangentTermV 16 27    + 
      ((13/27 : ℚ) : ℝ) * cotangentTermV 17 27    + 
      ((9/27 : ℚ) : ℝ) * cotangentTermV 18 27    + 
      ((5/27 : ℚ) : ℝ) * cotangentTermV 19 27    + 
      ((1/27 : ℚ) : ℝ) * cotangentTermV 20 27    + 
      ((24/27 : ℚ) : ℝ) * cotangentTermV 21 27    + 
      ((20/27 : ℚ) : ℝ) * cotangentTermV 22 27    + 
      ((16/27 : ℚ) : ℝ) * cotangentTermV 23 27    + 
      ((12/27 : ℚ) : ℝ) * cotangentTermV 24 27    + 
      ((8/27 : ℚ) : ℝ) * cotangentTermV 25 27    + 
      ((4/27 : ℚ) : ℝ) * cotangentTermV 26 27 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_27]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((23/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((19/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((15/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((11/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((7/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((3/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((26/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((22/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((18/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((14/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((10/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((6/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((2/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((25/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((21/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((17/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((13/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((9/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((5/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((1/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((24/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((20/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((16/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((12/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((8/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((4/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26]
  try ring

def cotangentSumVFormula_50_27_lower : ℚ := 3229338086995710910771 / 439804651110400000000
def cotangentSumVFormula_50_27_upper : ℚ := 3229338095791884401729 / 439804651110400000000
theorem cotangentSumVFormula_50_27_bounds :
  ((cotangentSumVFormula_50_27_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 27 ∧
  cotangentSumVFormula 50 27 ≤ ((cotangentSumVFormula_50_27_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_27_unfold]
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
  rw [cotangentSumVFormula_50_27_lower, cotangentSumVFormula_50_27_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2750_formula_bound :
  (((16194632358071469313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 27 50) ∧
  (vasyuninBEntryFormula 27 50 ≤ ((64783033031916169623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 27 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log27 := prim_log_27_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_27_50_bounds
  have b_Vkh := cotangentSumVFormula_50_27_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_27_lower, prim_log_27_upper] at b_log27
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_27_50_lower, cotangentSumVFormula_27_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_27_lower, cotangentSumVFormula_50_27_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_50_unfold :
    cotangentSumVFormula 29 50 =
      ((29/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 29 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_29_50_lower : ℚ := -2332086197764309979457 / 3518437208883200000000
def cotangentSumVFormula_29_50_upper : ℚ := -2332086127392646270543 / 3518437208883200000000
theorem cotangentSumVFormula_29_50_bounds :
  ((cotangentSumVFormula_29_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 50 ∧
  cotangentSumVFormula 29 50 ≤ ((cotangentSumVFormula_29_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_29_50_lower, cotangentSumVFormula_29_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_29_unfold :
    cotangentSumVFormula 50 29 =
      ((21/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_50_29_lower : ℚ := 2779846571596666743417 / 879609302220800000000
def cotangentSumVFormula_50_29_upper : ℚ := 2779846589189053569083 / 879609302220800000000
theorem cotangentSumVFormula_50_29_bounds :
  ((cotangentSumVFormula_50_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 29 ∧
  cotangentSumVFormula 50 29 ≤ ((cotangentSumVFormula_50_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_29_unfold]
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
  rw [cotangentSumVFormula_50_29_lower, cotangentSumVFormula_50_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2950_formula_bound :
  (((124709254151165051379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 50) ∧
  (vasyuninBEntryFormula 29 50 ≤ ((124718261350425323621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_29_50_bounds
  have b_Vkh := cotangentSumVFormula_50_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_29_50_lower, cotangentSumVFormula_29_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_29_lower, cotangentSumVFormula_50_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_50_unfold :
    cotangentSumVFormula 31 50 =
      ((31/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 31 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_31_50_lower : ℚ := 2129118718302059712167 / 879609302220800000000
def cotangentSumVFormula_31_50_upper : ℚ := 2129118735894943412833 / 879609302220800000000
theorem cotangentSumVFormula_31_50_bounds :
  ((cotangentSumVFormula_31_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 50 ∧
  cotangentSumVFormula 31 50 ≤ ((cotangentSumVFormula_31_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_31_50_lower, cotangentSumVFormula_31_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_31_unfold :
    cotangentSumVFormula 50 31 =
      ((19/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_50_31_lower : ℚ := 1112784980326202627459 / 1759218604441600000000
def cotangentSumVFormula_50_31_upper : ℚ := 1112785015511109872541 / 1759218604441600000000
theorem cotangentSumVFormula_50_31_bounds :
  ((cotangentSumVFormula_50_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 31 ∧
  cotangentSumVFormula 50 31 ≤ ((cotangentSumVFormula_50_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_31_unfold]
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
  rw [cotangentSumVFormula_50_31_lower, cotangentSumVFormula_50_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3150_formula_bound :
  (((121214067640227895129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 50) ∧
  (vasyuninBEntryFormula 31 50 ≤ ((121223074839487979871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_31_50_bounds
  have b_Vkh := cotangentSumVFormula_50_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_31_50_lower, cotangentSumVFormula_31_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_31_lower, cotangentSumVFormula_50_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_33_50_unfold :
    cotangentSumVFormula 33 50 =
      ((33/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 33 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_33_50_lower : ℚ := 635321485180658639237 / 54975581388800000000
def cotangentSumVFormula_33_50_upper : ℚ := 1270642972560432330901 / 109951162777600000000
theorem cotangentSumVFormula_33_50_bounds :
  ((cotangentSumVFormula_33_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 50 ∧
  cotangentSumVFormula 33 50 ≤ ((cotangentSumVFormula_33_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_33_50_lower, cotangentSumVFormula_33_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_33_unfold :
    cotangentSumVFormula 50 33 =
      ((17/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((2/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((5/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((7/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((10/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((13/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((14/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((16/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 50 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_50_33_lower : ℚ := -1817904401295051771177 / 219902325555200000000
def cotangentSumVFormula_50_33_upper : ℚ := -1817904396896934947573 / 219902325555200000000
theorem cotangentSumVFormula_50_33_bounds :
  ((cotangentSumVFormula_50_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 33 ∧
  cotangentSumVFormula 50 33 ≤ ((cotangentSumVFormula_50_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_33_unfold]
  have b_cot_1 := cot_pi_1_33_bounds
  simp only [cot_pi_1_33_lower, cot_pi_1_33_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_33_bounds
  simp only [cot_pi_2_33_lower, cot_pi_2_33_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_33_bounds
  simp only [cot_pi_3_33_lower, cot_pi_3_33_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_33_bounds
  simp only [cot_pi_4_33_lower, cot_pi_4_33_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_33_bounds
  simp only [cot_pi_5_33_lower, cot_pi_5_33_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_33_bounds
  simp only [cot_pi_6_33_lower, cot_pi_6_33_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_33_bounds
  simp only [cot_pi_7_33_lower, cot_pi_7_33_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_33_bounds
  simp only [cot_pi_8_33_lower, cot_pi_8_33_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_33_bounds
  simp only [cot_pi_9_33_lower, cot_pi_9_33_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_33_bounds
  simp only [cot_pi_10_33_lower, cot_pi_10_33_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_33_bounds
  simp only [cot_pi_11_33_lower, cot_pi_11_33_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_33_bounds
  simp only [cot_pi_12_33_lower, cot_pi_12_33_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_33_bounds
  simp only [cot_pi_13_33_lower, cot_pi_13_33_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_33_bounds
  simp only [cot_pi_14_33_lower, cot_pi_14_33_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_33_bounds
  simp only [cot_pi_15_33_lower, cot_pi_15_33_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_33_bounds
  simp only [cot_pi_16_33_lower, cot_pi_16_33_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_33_bounds
  simp only [cot_pi_17_33_lower, cot_pi_17_33_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_33_bounds
  simp only [cot_pi_18_33_lower, cot_pi_18_33_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_33_bounds
  simp only [cot_pi_19_33_lower, cot_pi_19_33_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_33_bounds
  simp only [cot_pi_20_33_lower, cot_pi_20_33_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_33_bounds
  simp only [cot_pi_21_33_lower, cot_pi_21_33_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_33_bounds
  simp only [cot_pi_22_33_lower, cot_pi_22_33_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_33_bounds
  simp only [cot_pi_23_33_lower, cot_pi_23_33_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_33_bounds
  simp only [cot_pi_24_33_lower, cot_pi_24_33_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_33_bounds
  simp only [cot_pi_25_33_lower, cot_pi_25_33_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_33_bounds
  simp only [cot_pi_26_33_lower, cot_pi_26_33_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_33_bounds
  simp only [cot_pi_27_33_lower, cot_pi_27_33_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_33_bounds
  simp only [cot_pi_28_33_lower, cot_pi_28_33_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_33_bounds
  simp only [cot_pi_29_33_lower, cot_pi_29_33_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_33_bounds
  simp only [cot_pi_30_33_lower, cot_pi_30_33_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_33_bounds
  simp only [cot_pi_31_33_lower, cot_pi_31_33_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_33_bounds
  simp only [cot_pi_32_33_lower, cot_pi_32_33_upper] at b_cot_32
  rw [cotangentSumVFormula_50_33_lower, cotangentSumVFormula_50_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3350_formula_bound :
  (((29762441159052516751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 50) ∧
  (vasyuninBEntryFormula 33 50 ≤ ((59529385917735044623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_33_50_bounds
  have b_Vkh := cotangentSumVFormula_50_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_33_50_lower, cotangentSumVFormula_33_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_33_lower, cotangentSumVFormula_50_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_50_unfold :
    cotangentSumVFormula 37 50 =
      ((37/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 37 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_37_50_lower : ℚ := 1909037410612770103823 / 219902325555200000000
def cotangentSumVFormula_37_50_upper : ℚ := 1909037415010976771177 / 219902325555200000000
theorem cotangentSumVFormula_37_50_bounds :
  ((cotangentSumVFormula_37_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 50 ∧
  cotangentSumVFormula 37 50 ≤ ((cotangentSumVFormula_37_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_37_50_lower, cotangentSumVFormula_37_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_37_unfold :
    cotangentSumVFormula 50 37 =
      ((13/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 50 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_50_37_lower : ℚ := -1049993229841402552427 / 219902325555200000000
def cotangentSumVFormula_50_37_upper : ℚ := -1049993225443271666323 / 219902325555200000000
theorem cotangentSumVFormula_50_37_bounds :
  ((cotangentSumVFormula_50_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 37 ∧
  cotangentSumVFormula 50 37 ≤ ((cotangentSumVFormula_50_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_37_unfold]
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
  rw [cotangentSumVFormula_50_37_lower, cotangentSumVFormula_50_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3750_formula_bound :
  (((113791240359081770129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 50) ∧
  (vasyuninBEntryFormula 37 50 ≤ ((113800247558341073621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_37_50_bounds
  have b_Vkh := cotangentSumVFormula_50_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_37_50_lower, cotangentSumVFormula_37_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_37_lower, cotangentSumVFormula_50_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_39_50_unfold :
    cotangentSumVFormula 39 50 =
      ((39/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 39 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_39_50_lower : ℚ := 2872061487849591379521 / 439804651110400000000
def cotangentSumVFormula_39_50_upper : ℚ := 2872061496646002370479 / 439804651110400000000
theorem cotangentSumVFormula_39_50_bounds :
  ((cotangentSumVFormula_39_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 50 ∧
  cotangentSumVFormula 39 50 ≤ ((cotangentSumVFormula_39_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_39_50_lower, cotangentSumVFormula_39_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_39_unfold :
    cotangentSumVFormula 50 39 =
      ((11/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 50 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_50_39_lower : ℚ := -279675822909583112151 / 109951162777600000000
def cotangentSumVFormula_50_39_upper : ℚ := -559351641420995885073 / 219902325555200000000
theorem cotangentSumVFormula_50_39_bounds :
  ((cotangentSumVFormula_50_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 39 ∧
  cotangentSumVFormula 50 39 ≤ ((cotangentSumVFormula_50_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_39_unfold]
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
  rw [cotangentSumVFormula_50_39_lower, cotangentSumVFormula_50_39_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3950_formula_bound :
  (((3498134235032160297 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 39 50) ∧
  (vasyuninBEntryFormula 39 50 ≤ ((27987325680072201999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 39 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log39 := prim_log_39_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_39_50_bounds
  have b_Vkh := cotangentSumVFormula_50_39_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_39_50_lower, cotangentSumVFormula_39_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_39_lower, cotangentSumVFormula_50_39_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_50_unfold :
    cotangentSumVFormula 41 50 =
      ((41/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 41 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_41_50_lower : ℚ := 523861304851818795487 / 54975581388800000000
def cotangentSumVFormula_41_50_upper : ℚ := 1047722611902735455901 / 109951162777600000000
theorem cotangentSumVFormula_41_50_bounds :
  ((cotangentSumVFormula_41_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 50 ∧
  cotangentSumVFormula 41 50 ≤ ((cotangentSumVFormula_41_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_41_50_lower, cotangentSumVFormula_41_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_41_unfold :
    cotangentSumVFormula 50 41 =
      ((9/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((4/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((8/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((3/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((2/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((6/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((1/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((5/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 50 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_50_41_lower : ℚ := -2476107121607315651729 / 439804651110400000000
def cotangentSumVFormula_50_41_upper : ℚ := -2476107112810984348271 / 439804651110400000000
theorem cotangentSumVFormula_50_41_bounds :
  ((cotangentSumVFormula_50_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 41 ∧
  cotangentSumVFormula 50 41 ≤ ((cotangentSumVFormula_50_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_41_unfold]
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
  rw [cotangentSumVFormula_50_41_lower, cotangentSumVFormula_50_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4150_formula_bound :
  (((110592003356145863879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 50) ∧
  (vasyuninBEntryFormula 41 50 ≤ ((110601010555405136121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_41_50_bounds
  have b_Vkh := cotangentSumVFormula_50_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_41_50_lower, cotangentSumVFormula_41_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_41_lower, cotangentSumVFormula_50_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_43_50_unfold :
    cotangentSumVFormula 43 50 =
      ((43/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 43 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_43_50_lower : ℚ := 1276205880899402825349 / 109951162777600000000
def cotangentSumVFormula_43_50_upper : ℚ := 1276205883098508112151 / 109951162777600000000
theorem cotangentSumVFormula_43_50_bounds :
  ((cotangentSumVFormula_43_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 50 ∧
  cotangentSumVFormula 43 50 ≤ ((cotangentSumVFormula_43_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_43_50_lower, cotangentSumVFormula_43_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_43_unfold :
    cotangentSumVFormula 50 43 =
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
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 50 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_50_43_lower : ℚ := -3506335817518192995479 / 439804651110400000000
def cotangentSumVFormula_50_43_upper : ℚ := -3506335808721740598271 / 439804651110400000000
theorem cotangentSumVFormula_50_43_bounds :
  ((cotangentSumVFormula_50_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 43 ∧
  cotangentSumVFormula 50 43 ≤ ((cotangentSumVFormula_50_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_43_unfold]
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
  rw [cotangentSumVFormula_50_43_lower, cotangentSumVFormula_50_43_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4350_formula_bound :
  (((27430902992453641751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 43 50) ∧
  (vasyuninBEntryFormula 43 50 ≤ ((54866309584537357123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 43 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log43 := log_43_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_43_50_bounds
  have b_Vkh := cotangentSumVFormula_50_43_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_43_50_lower, cotangentSumVFormula_43_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_43_lower, cotangentSumVFormula_50_43_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_47_50_unfold :
    cotangentSumVFormula 47 50 =
      ((47/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 47 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_47_50_lower : ℚ := 2843025965619892669099 / 109951162777600000000
def cotangentSumVFormula_47_50_upper : ℚ := 2843025967819001862151 / 109951162777600000000
theorem cotangentSumVFormula_47_50_bounds :
  ((cotangentSumVFormula_47_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 50 ∧
  cotangentSumVFormula 47 50 ≤ ((cotangentSumVFormula_47_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_47_50_lower, cotangentSumVFormula_47_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_47_unfold :
    cotangentSumVFormula 50 47 =
      ((3/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 50 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_50_47_lower : ℚ := -2578191821266652643401 / 109951162777600000000
def cotangentSumVFormula_50_47_upper : ℚ := -2578191819067520012849 / 109951162777600000000
theorem cotangentSumVFormula_50_47_bounds :
  ((cotangentSumVFormula_50_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 47 ∧
  cotangentSumVFormula 50 47 ≤ ((cotangentSumVFormula_50_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_47_unfold]
  have b_cot_1 := cot_pi_1_47_bounds
  simp only [cot_pi_1_47_lower, cot_pi_1_47_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_47_bounds
  simp only [cot_pi_2_47_lower, cot_pi_2_47_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_47_bounds
  simp only [cot_pi_3_47_lower, cot_pi_3_47_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_47_bounds
  simp only [cot_pi_4_47_lower, cot_pi_4_47_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_47_bounds
  simp only [cot_pi_5_47_lower, cot_pi_5_47_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_47_bounds
  simp only [cot_pi_6_47_lower, cot_pi_6_47_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_47_bounds
  simp only [cot_pi_7_47_lower, cot_pi_7_47_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_47_bounds
  simp only [cot_pi_8_47_lower, cot_pi_8_47_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_47_bounds
  simp only [cot_pi_9_47_lower, cot_pi_9_47_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_47_bounds
  simp only [cot_pi_10_47_lower, cot_pi_10_47_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_47_bounds
  simp only [cot_pi_11_47_lower, cot_pi_11_47_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_47_bounds
  simp only [cot_pi_12_47_lower, cot_pi_12_47_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_47_bounds
  simp only [cot_pi_13_47_lower, cot_pi_13_47_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_47_bounds
  simp only [cot_pi_14_47_lower, cot_pi_14_47_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_47_bounds
  simp only [cot_pi_15_47_lower, cot_pi_15_47_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_47_bounds
  simp only [cot_pi_16_47_lower, cot_pi_16_47_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_47_bounds
  simp only [cot_pi_17_47_lower, cot_pi_17_47_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_47_bounds
  simp only [cot_pi_18_47_lower, cot_pi_18_47_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_47_bounds
  simp only [cot_pi_19_47_lower, cot_pi_19_47_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_47_bounds
  simp only [cot_pi_20_47_lower, cot_pi_20_47_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_47_bounds
  simp only [cot_pi_21_47_lower, cot_pi_21_47_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_47_bounds
  simp only [cot_pi_22_47_lower, cot_pi_22_47_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_47_bounds
  simp only [cot_pi_23_47_lower, cot_pi_23_47_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_47_bounds
  simp only [cot_pi_24_47_lower, cot_pi_24_47_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_47_bounds
  simp only [cot_pi_25_47_lower, cot_pi_25_47_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_47_bounds
  simp only [cot_pi_26_47_lower, cot_pi_26_47_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_47_bounds
  simp only [cot_pi_27_47_lower, cot_pi_27_47_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_47_bounds
  simp only [cot_pi_28_47_lower, cot_pi_28_47_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_47_bounds
  simp only [cot_pi_29_47_lower, cot_pi_29_47_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_47_bounds
  simp only [cot_pi_30_47_lower, cot_pi_30_47_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_47_bounds
  simp only [cot_pi_31_47_lower, cot_pi_31_47_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_47_bounds
  simp only [cot_pi_32_47_lower, cot_pi_32_47_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_47_bounds
  simp only [cot_pi_33_47_lower, cot_pi_33_47_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_47_bounds
  simp only [cot_pi_34_47_lower, cot_pi_34_47_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_47_bounds
  simp only [cot_pi_35_47_lower, cot_pi_35_47_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_47_bounds
  simp only [cot_pi_36_47_lower, cot_pi_36_47_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_47_bounds
  simp only [cot_pi_37_47_lower, cot_pi_37_47_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_47_bounds
  simp only [cot_pi_38_47_lower, cot_pi_38_47_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_47_bounds
  simp only [cot_pi_39_47_lower, cot_pi_39_47_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_47_bounds
  simp only [cot_pi_40_47_lower, cot_pi_40_47_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_47_bounds
  simp only [cot_pi_41_47_lower, cot_pi_41_47_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_47_bounds
  simp only [cot_pi_42_47_lower, cot_pi_42_47_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_47_bounds
  simp only [cot_pi_43_47_lower, cot_pi_43_47_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_47_bounds
  simp only [cot_pi_44_47_lower, cot_pi_44_47_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_47_bounds
  simp only [cot_pi_45_47_lower, cot_pi_45_47_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_47_bounds
  simp only [cot_pi_46_47_lower, cot_pi_46_47_upper] at b_cot_46
  rw [cotangentSumVFormula_50_47_lower, cotangentSumVFormula_50_47_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4750_formula_bound :
  (((6858816020761054969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 47 50) ∧
  (vasyuninBEntryFormula 47 50 ≤ ((13718757941429655687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 47 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log47 := log_47_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_47_50_bounds
  have b_Vkh := cotangentSumVFormula_50_47_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_47_50_lower, cotangentSumVFormula_47_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_47_lower, cotangentSumVFormula_50_47_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_49_50_unfold :
    cotangentSumVFormula 49 50 =
      ((49/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 49 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_49_50_lower : ℚ := 146089999189328933507 / 3435973836800000000
def cotangentSumVFormula_49_50_upper : ℚ := 73044999629025572309 / 1717986918400000000
theorem cotangentSumVFormula_49_50_bounds :
  ((cotangentSumVFormula_49_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 50 ∧
  cotangentSumVFormula 49 50 ≤ ((cotangentSumVFormula_49_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_50_unfold]
  have b_cot_1 := cot_pi_1_50_bounds
  simp only [cot_pi_1_50_lower, cot_pi_1_50_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_50_bounds
  simp only [cot_pi_2_50_lower, cot_pi_2_50_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_50_bounds
  simp only [cot_pi_3_50_lower, cot_pi_3_50_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_50_bounds
  simp only [cot_pi_4_50_lower, cot_pi_4_50_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_50_bounds
  simp only [cot_pi_5_50_lower, cot_pi_5_50_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_50_bounds
  simp only [cot_pi_6_50_lower, cot_pi_6_50_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_50_bounds
  simp only [cot_pi_7_50_lower, cot_pi_7_50_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_50_bounds
  simp only [cot_pi_8_50_lower, cot_pi_8_50_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_50_bounds
  simp only [cot_pi_9_50_lower, cot_pi_9_50_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_50_bounds
  simp only [cot_pi_10_50_lower, cot_pi_10_50_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_50_bounds
  simp only [cot_pi_11_50_lower, cot_pi_11_50_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_50_bounds
  simp only [cot_pi_12_50_lower, cot_pi_12_50_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_50_bounds
  simp only [cot_pi_13_50_lower, cot_pi_13_50_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_50_bounds
  simp only [cot_pi_14_50_lower, cot_pi_14_50_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_50_bounds
  simp only [cot_pi_15_50_lower, cot_pi_15_50_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_50_bounds
  simp only [cot_pi_16_50_lower, cot_pi_16_50_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_50_bounds
  simp only [cot_pi_17_50_lower, cot_pi_17_50_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_50_bounds
  simp only [cot_pi_18_50_lower, cot_pi_18_50_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_50_bounds
  simp only [cot_pi_19_50_lower, cot_pi_19_50_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_50_bounds
  simp only [cot_pi_20_50_lower, cot_pi_20_50_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_50_bounds
  simp only [cot_pi_21_50_lower, cot_pi_21_50_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_50_bounds
  simp only [cot_pi_22_50_lower, cot_pi_22_50_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_50_bounds
  simp only [cot_pi_23_50_lower, cot_pi_23_50_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_50_bounds
  simp only [cot_pi_24_50_lower, cot_pi_24_50_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_50_bounds
  simp only [cot_pi_25_50_lower, cot_pi_25_50_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_50_bounds
  simp only [cot_pi_26_50_lower, cot_pi_26_50_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_50_bounds
  simp only [cot_pi_27_50_lower, cot_pi_27_50_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_50_bounds
  simp only [cot_pi_28_50_lower, cot_pi_28_50_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_50_bounds
  simp only [cot_pi_29_50_lower, cot_pi_29_50_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_50_bounds
  simp only [cot_pi_30_50_lower, cot_pi_30_50_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_50_bounds
  simp only [cot_pi_31_50_lower, cot_pi_31_50_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_50_bounds
  simp only [cot_pi_32_50_lower, cot_pi_32_50_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_50_bounds
  simp only [cot_pi_33_50_lower, cot_pi_33_50_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_50_bounds
  simp only [cot_pi_34_50_lower, cot_pi_34_50_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_50_bounds
  simp only [cot_pi_35_50_lower, cot_pi_35_50_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_50_bounds
  simp only [cot_pi_36_50_lower, cot_pi_36_50_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_50_bounds
  simp only [cot_pi_37_50_lower, cot_pi_37_50_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_50_bounds
  simp only [cot_pi_38_50_lower, cot_pi_38_50_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_50_bounds
  simp only [cot_pi_39_50_lower, cot_pi_39_50_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_50_bounds
  simp only [cot_pi_40_50_lower, cot_pi_40_50_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_50_bounds
  simp only [cot_pi_41_50_lower, cot_pi_41_50_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_50_bounds
  simp only [cot_pi_42_50_lower, cot_pi_42_50_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_50_bounds
  simp only [cot_pi_43_50_lower, cot_pi_43_50_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_50_bounds
  simp only [cot_pi_44_50_lower, cot_pi_44_50_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_50_bounds
  simp only [cot_pi_45_50_lower, cot_pi_45_50_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_50_bounds
  simp only [cot_pi_46_50_lower, cot_pi_46_50_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_50_bounds
  simp only [cot_pi_47_50_lower, cot_pi_47_50_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_50_bounds
  simp only [cot_pi_48_50_lower, cot_pi_48_50_upper] at b_cot_48
  have b_cot_49 := cot_pi_49_50_bounds
  simp only [cot_pi_49_50_lower, cot_pi_49_50_upper] at b_cot_49
  rw [cotangentSumVFormula_49_50_lower, cotangentSumVFormula_49_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_49_unfold :
    cotangentSumVFormula 50 49 =
      ((1/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 50 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_50_49_lower : ℚ := -1136860975427551735069 / 27487790694400000000
def cotangentSumVFormula_50_49_upper : ℚ := -568430487438887218403 / 13743895347200000000
theorem cotangentSumVFormula_50_49_bounds :
  ((cotangentSumVFormula_50_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 49 ∧
  cotangentSumVFormula 50 49 ≤ ((cotangentSumVFormula_50_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_49_unfold]
  have b_cot_1 := cot_pi_1_49_bounds
  simp only [cot_pi_1_49_lower, cot_pi_1_49_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_49_bounds
  simp only [cot_pi_2_49_lower, cot_pi_2_49_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_49_bounds
  simp only [cot_pi_3_49_lower, cot_pi_3_49_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_49_bounds
  simp only [cot_pi_4_49_lower, cot_pi_4_49_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_49_bounds
  simp only [cot_pi_5_49_lower, cot_pi_5_49_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_49_bounds
  simp only [cot_pi_6_49_lower, cot_pi_6_49_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_49_bounds
  simp only [cot_pi_7_49_lower, cot_pi_7_49_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_49_bounds
  simp only [cot_pi_8_49_lower, cot_pi_8_49_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_49_bounds
  simp only [cot_pi_9_49_lower, cot_pi_9_49_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_49_bounds
  simp only [cot_pi_10_49_lower, cot_pi_10_49_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_49_bounds
  simp only [cot_pi_11_49_lower, cot_pi_11_49_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_49_bounds
  simp only [cot_pi_12_49_lower, cot_pi_12_49_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_49_bounds
  simp only [cot_pi_13_49_lower, cot_pi_13_49_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_49_bounds
  simp only [cot_pi_14_49_lower, cot_pi_14_49_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_49_bounds
  simp only [cot_pi_15_49_lower, cot_pi_15_49_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_49_bounds
  simp only [cot_pi_16_49_lower, cot_pi_16_49_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_49_bounds
  simp only [cot_pi_17_49_lower, cot_pi_17_49_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_49_bounds
  simp only [cot_pi_18_49_lower, cot_pi_18_49_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_49_bounds
  simp only [cot_pi_19_49_lower, cot_pi_19_49_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_49_bounds
  simp only [cot_pi_20_49_lower, cot_pi_20_49_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_49_bounds
  simp only [cot_pi_21_49_lower, cot_pi_21_49_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_49_bounds
  simp only [cot_pi_22_49_lower, cot_pi_22_49_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_49_bounds
  simp only [cot_pi_23_49_lower, cot_pi_23_49_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_49_bounds
  simp only [cot_pi_24_49_lower, cot_pi_24_49_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_49_bounds
  simp only [cot_pi_25_49_lower, cot_pi_25_49_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_49_bounds
  simp only [cot_pi_26_49_lower, cot_pi_26_49_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_49_bounds
  simp only [cot_pi_27_49_lower, cot_pi_27_49_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_49_bounds
  simp only [cot_pi_28_49_lower, cot_pi_28_49_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_49_bounds
  simp only [cot_pi_29_49_lower, cot_pi_29_49_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_49_bounds
  simp only [cot_pi_30_49_lower, cot_pi_30_49_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_49_bounds
  simp only [cot_pi_31_49_lower, cot_pi_31_49_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_49_bounds
  simp only [cot_pi_32_49_lower, cot_pi_32_49_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_49_bounds
  simp only [cot_pi_33_49_lower, cot_pi_33_49_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_49_bounds
  simp only [cot_pi_34_49_lower, cot_pi_34_49_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_49_bounds
  simp only [cot_pi_35_49_lower, cot_pi_35_49_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_49_bounds
  simp only [cot_pi_36_49_lower, cot_pi_36_49_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_49_bounds
  simp only [cot_pi_37_49_lower, cot_pi_37_49_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_49_bounds
  simp only [cot_pi_38_49_lower, cot_pi_38_49_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_49_bounds
  simp only [cot_pi_39_49_lower, cot_pi_39_49_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_49_bounds
  simp only [cot_pi_40_49_lower, cot_pi_40_49_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_49_bounds
  simp only [cot_pi_41_49_lower, cot_pi_41_49_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_49_bounds
  simp only [cot_pi_42_49_lower, cot_pi_42_49_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_49_bounds
  simp only [cot_pi_43_49_lower, cot_pi_43_49_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_49_bounds
  simp only [cot_pi_44_49_lower, cot_pi_44_49_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_49_bounds
  simp only [cot_pi_45_49_lower, cot_pi_45_49_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_49_bounds
  simp only [cot_pi_46_49_lower, cot_pi_46_49_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_49_bounds
  simp only [cot_pi_47_49_lower, cot_pi_47_49_upper] at b_cot_47
  have b_cot_48 := cot_pi_48_49_bounds
  simp only [cot_pi_48_49_lower, cot_pi_48_49_upper] at b_cot_48
  rw [cotangentSumVFormula_50_49_lower, cotangentSumVFormula_50_49_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4950_formula_bound :
  (((13917408864170750563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 49 50) ∧
  (vasyuninBEntryFormula 49 50 ≤ ((55674139056312794623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 49 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log49 := prim_log_49_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_49_50_bounds
  have b_Vkh := cotangentSumVFormula_50_49_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_49_50_lower, cotangentSumVFormula_49_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_49_lower, cotangentSumVFormula_50_49_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
