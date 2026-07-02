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

theorem cotangentSumVFormula_11_49_unfold :
    cotangentSumVFormula 11 49 =
      ((11/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 11 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_11_49_lower : ℚ := -1768044271621833021177 / 219902325555200000000
def cotangentSumVFormula_11_49_upper : ℚ := -1768044267223613072573 / 219902325555200000000
theorem cotangentSumVFormula_11_49_bounds :
  ((cotangentSumVFormula_11_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 49 ∧
  cotangentSumVFormula 11 49 ≤ ((cotangentSumVFormula_11_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_49_unfold]
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
  rw [cotangentSumVFormula_11_49_lower, cotangentSumVFormula_11_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_11_unfold :
    cotangentSumVFormula 49 11 =
      ((5/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_49_11_lower : ℚ := 1675571378290838564959 / 1759218604441600000000
def cotangentSumVFormula_49_11_upper : ℚ := 1675571413475262216291 / 1759218604441600000000
theorem cotangentSumVFormula_49_11_bounds :
  ((cotangentSumVFormula_49_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 11 ∧
  cotangentSumVFormula 49 11 ≤ ((cotangentSumVFormula_49_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_11_unfold]
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
  rw [cotangentSumVFormula_49_11_lower, cotangentSumVFormula_49_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1149_formula_bound :
  (((42963908176243516751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 49) ∧
  (vasyuninBEntryFormula 11 49 ≤ ((21483079988030061937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_11_49_bounds
  have b_Vkh := cotangentSumVFormula_49_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_11_49_lower, cotangentSumVFormula_11_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_11_lower, cotangentSumVFormula_49_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_12_49_unfold :
    cotangentSumVFormula 12 49 =
      ((12/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 12 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_12_49_lower : ℚ := -2083277973449802841291 / 1759218604441600000000
def cotangentSumVFormula_12_49_upper : ℚ := -2083277938264072158709 / 1759218604441600000000
theorem cotangentSumVFormula_12_49_bounds :
  ((cotangentSumVFormula_12_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 49 ∧
  cotangentSumVFormula 12 49 ≤ ((cotangentSumVFormula_12_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_49_unfold]
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
  rw [cotangentSumVFormula_12_49_lower, cotangentSumVFormula_12_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_12_unfold :
    cotangentSumVFormula 49 12 =
      ((1/12 : ℚ) : ℝ) * cotangentTermV 1 12    + 
      ((2/12 : ℚ) : ℝ) * cotangentTermV 2 12    + 
      ((3/12 : ℚ) : ℝ) * cotangentTermV 3 12    + 
      ((4/12 : ℚ) : ℝ) * cotangentTermV 4 12    + 
      ((5/12 : ℚ) : ℝ) * cotangentTermV 5 12    + 
      ((6/12 : ℚ) : ℝ) * cotangentTermV 6 12    + 
      ((7/12 : ℚ) : ℝ) * cotangentTermV 7 12    + 
      ((8/12 : ℚ) : ℝ) * cotangentTermV 8 12    + 
      ((9/12 : ℚ) : ℝ) * cotangentTermV 9 12    + 
      ((10/12 : ℚ) : ℝ) * cotangentTermV 10 12    + 
      ((11/12 : ℚ) : ℝ) * cotangentTermV 11 12 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_12]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_49_12_lower : ℚ := -34372459555962836111 / 6871947673600000000
def cotangentSumVFormula_49_12_upper : ℚ := -1099918701392752135073 / 219902325555200000000
theorem cotangentSumVFormula_49_12_bounds :
  ((cotangentSumVFormula_49_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 12 ∧
  cotangentSumVFormula 49 12 ≤ ((cotangentSumVFormula_49_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_12_unfold]
  have b_cot_1 := cot_pi_1_12_bounds
  simp only [cot_pi_1_12_lower, cot_pi_1_12_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_12_bounds
  simp only [cot_pi_2_12_lower, cot_pi_2_12_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_12_bounds
  simp only [cot_pi_3_12_lower, cot_pi_3_12_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_12_bounds
  simp only [cot_pi_4_12_lower, cot_pi_4_12_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_12_bounds
  simp only [cot_pi_5_12_lower, cot_pi_5_12_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_12_bounds
  simp only [cot_pi_6_12_lower, cot_pi_6_12_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_12_bounds
  simp only [cot_pi_7_12_lower, cot_pi_7_12_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_12_bounds
  simp only [cot_pi_8_12_lower, cot_pi_8_12_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_12_bounds
  simp only [cot_pi_9_12_lower, cot_pi_9_12_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_12_bounds
  simp only [cot_pi_10_12_lower, cot_pi_10_12_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_12_bounds
  simp only [cot_pi_11_12_lower, cot_pi_11_12_upper] at b_cot_11
  rw [cotangentSumVFormula_49_12_lower, cotangentSumVFormula_49_12_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1249_formula_bound :
  (((84782249691355611627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 12 49) ∧
  (vasyuninBEntryFormula 12 49 ≤ ((84786753290988419623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 12 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log12 := prim_log_12_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_12_49_bounds
  have b_Vkh := cotangentSumVFormula_49_12_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_12_49_lower, cotangentSumVFormula_12_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_12_lower, cotangentSumVFormula_49_12_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_49_unfold :
    cotangentSumVFormula 13 49 =
      ((13/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 13 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_13_49_lower : ℚ := -2960337463440743776729 / 439804651110400000000
def cotangentSumVFormula_13_49_upper : ℚ := -2960337454644308567021 / 439804651110400000000
theorem cotangentSumVFormula_13_49_bounds :
  ((cotangentSumVFormula_13_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 49 ∧
  cotangentSumVFormula 13 49 ≤ ((cotangentSumVFormula_13_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_49_unfold]
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
  rw [cotangentSumVFormula_13_49_lower, cotangentSumVFormula_13_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_13_unfold :
    cotangentSumVFormula 49 13 =
      ((10/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_49_13_lower : ℚ := 1410513581720014399667 / 879609302220800000000
def cotangentSumVFormula_49_13_upper : ℚ := 705256799656120339229 / 439804651110400000000
theorem cotangentSumVFormula_49_13_bounds :
  ((cotangentSumVFormula_49_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 13 ∧
  cotangentSumVFormula 49 13 ≤ ((cotangentSumVFormula_49_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_13_unfold]
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
  rw [cotangentSumVFormula_49_13_lower, cotangentSumVFormula_49_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1349_formula_bound :
  (((2568446405319025461 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 49) ∧
  (vasyuninBEntryFormula 13 49 ≤ ((41097394284920576999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_13_49_bounds
  have b_Vkh := cotangentSumVFormula_49_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_13_49_lower, cotangentSumVFormula_13_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_13_lower, cotangentSumVFormula_49_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_49_unfold :
    cotangentSumVFormula 15 49 =
      ((15/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 15 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_15_49_lower : ℚ := -2588665747900370028791 / 1759218604441600000000
def cotangentSumVFormula_15_49_upper : ℚ := -2588665712714654971209 / 1759218604441600000000
theorem cotangentSumVFormula_15_49_bounds :
  ((cotangentSumVFormula_15_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 49 ∧
  cotangentSumVFormula 15 49 ≤ ((cotangentSumVFormula_15_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_49_unfold]
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
  rw [cotangentSumVFormula_15_49_lower, cotangentSumVFormula_15_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_15_unfold :
    cotangentSumVFormula 49 15 =
      ((4/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_49_15_lower : ℚ := -901893767119739870479 / 439804651110400000000
def cotangentSumVFormula_49_15_upper : ℚ := -450946879161809166323 / 219902325555200000000
theorem cotangentSumVFormula_49_15_bounds :
  ((cotangentSumVFormula_49_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 15 ∧
  cotangentSumVFormula 49 15 ≤ ((cotangentSumVFormula_49_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_15_unfold]
  have b_cot_1 := cot_pi_1_15_bounds
  simp only [cot_pi_1_15_lower, cot_pi_1_15_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_15_bounds
  simp only [cot_pi_2_15_lower, cot_pi_2_15_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_15_bounds
  simp only [cot_pi_3_15_lower, cot_pi_3_15_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_15_bounds
  simp only [cot_pi_4_15_lower, cot_pi_4_15_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_15_bounds
  simp only [cot_pi_5_15_lower, cot_pi_5_15_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_15_bounds
  simp only [cot_pi_6_15_lower, cot_pi_6_15_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_15_bounds
  simp only [cot_pi_7_15_lower, cot_pi_7_15_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_15_bounds
  simp only [cot_pi_8_15_lower, cot_pi_8_15_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_15_bounds
  simp only [cot_pi_9_15_lower, cot_pi_9_15_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_15_bounds
  simp only [cot_pi_10_15_lower, cot_pi_10_15_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_15_bounds
  simp only [cot_pi_11_15_lower, cot_pi_11_15_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_15_bounds
  simp only [cot_pi_12_15_lower, cot_pi_12_15_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_15_bounds
  simp only [cot_pi_13_15_lower, cot_pi_13_15_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_15_bounds
  simp only [cot_pi_14_15_lower, cot_pi_14_15_upper] at b_cot_14
  rw [cotangentSumVFormula_49_15_lower, cotangentSumVFormula_49_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1549_formula_bound :
  (((39443148218851829251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 49) ∧
  (vasyuninBEntryFormula 15 49 ≤ ((19722700009333843187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_15_49_bounds
  have b_Vkh := cotangentSumVFormula_49_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_15_49_lower, cotangentSumVFormula_15_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_15_lower, cotangentSumVFormula_49_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_16_49_unfold :
    cotangentSumVFormula 16 49 =
      ((16/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 16 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_16_49_lower : ℚ := 2170830623302049192021 / 439804651110400000000
def cotangentSumVFormula_16_49_upper : ℚ := 2170830632098467995479 / 439804651110400000000
theorem cotangentSumVFormula_16_49_bounds :
  ((cotangentSumVFormula_16_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 49 ∧
  cotangentSumVFormula 16 49 ≤ ((cotangentSumVFormula_16_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_49_unfold]
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
  rw [cotangentSumVFormula_16_49_lower, cotangentSumVFormula_16_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_16_unfold :
    cotangentSumVFormula 49 16 =
      ((1/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_49_16_lower : ℚ := -1764484223855254114927 / 219902325555200000000
def cotangentSumVFormula_49_16_upper : ℚ := -1764484219457194322573 / 219902325555200000000
theorem cotangentSumVFormula_49_16_bounds :
  ((cotangentSumVFormula_49_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 16 ∧
  cotangentSumVFormula 49 16 ≤ ((cotangentSumVFormula_49_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_16_unfold]
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
  rw [cotangentSumVFormula_49_16_lower, cotangentSumVFormula_49_16_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1649_formula_bound :
  (((39283114189153735501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 16 49) ∧
  (vasyuninBEntryFormula 16 49 ≤ ((39285365988969389499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 16 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log16 := prim_log_16_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_16_49_bounds
  have b_Vkh := cotangentSumVFormula_49_16_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_16_49_lower, cotangentSumVFormula_16_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_16_lower, cotangentSumVFormula_49_16_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_49_unfold :
    cotangentSumVFormula 17 49 =
      ((17/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 17 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_17_49_lower : ℚ := -3393968849073792995479 / 439804651110400000000
def cotangentSumVFormula_17_49_upper : ℚ := -3393968840277363254521 / 439804651110400000000
theorem cotangentSumVFormula_17_49_bounds :
  ((cotangentSumVFormula_17_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 49 ∧
  cotangentSumVFormula 17 49 ≤ ((cotangentSumVFormula_17_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_49_unfold]
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
  rw [cotangentSumVFormula_17_49_lower, cotangentSumVFormula_17_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_17_unfold :
    cotangentSumVFormula 49 17 =
      ((15/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_49_17_lower : ℚ := 148235115050011546181 / 27487790694400000000
def cotangentSumVFormula_49_17_upper : ℚ := 296470231199539017013 / 54975581388800000000
theorem cotangentSumVFormula_49_17_bounds :
  ((cotangentSumVFormula_49_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 17 ∧
  cotangentSumVFormula 49 17 ≤ ((cotangentSumVFormula_49_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_17_unfold]
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
  rw [cotangentSumVFormula_49_17_lower, cotangentSumVFormula_49_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1749_formula_bound :
  (((38270018162334735501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 49) ∧
  (vasyuninBEntryFormula 17 49 ≤ ((38272269962150358249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_17_49_bounds
  have b_Vkh := cotangentSumVFormula_49_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_17_49_lower, cotangentSumVFormula_17_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_17_lower, cotangentSumVFormula_49_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_18_49_unfold :
    cotangentSumVFormula 18 49 =
      ((18/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 18 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_18_49_lower : ℚ := -729859622401946302427 / 219902325555200000000
def cotangentSumVFormula_18_49_upper : ℚ := -91232452250467014931 / 27487790694400000000
theorem cotangentSumVFormula_18_49_bounds :
  ((cotangentSumVFormula_18_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 49 ∧
  cotangentSumVFormula 18 49 ≤ ((cotangentSumVFormula_18_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_49_unfold]
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
  rw [cotangentSumVFormula_18_49_lower, cotangentSumVFormula_18_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_18_unfold :
    cotangentSumVFormula 49 18 =
      ((13/18 : ℚ) : ℝ) * cotangentTermV 1 18    + 
      ((8/18 : ℚ) : ℝ) * cotangentTermV 2 18    + 
      ((3/18 : ℚ) : ℝ) * cotangentTermV 3 18    + 
      ((16/18 : ℚ) : ℝ) * cotangentTermV 4 18    + 
      ((11/18 : ℚ) : ℝ) * cotangentTermV 5 18    + 
      ((6/18 : ℚ) : ℝ) * cotangentTermV 6 18    + 
      ((1/18 : ℚ) : ℝ) * cotangentTermV 7 18    + 
      ((14/18 : ℚ) : ℝ) * cotangentTermV 8 18    + 
      ((9/18 : ℚ) : ℝ) * cotangentTermV 9 18    + 
      ((4/18 : ℚ) : ℝ) * cotangentTermV 10 18    + 
      ((17/18 : ℚ) : ℝ) * cotangentTermV 11 18    + 
      ((12/18 : ℚ) : ℝ) * cotangentTermV 12 18    + 
      ((7/18 : ℚ) : ℝ) * cotangentTermV 13 18    + 
      ((2/18 : ℚ) : ℝ) * cotangentTermV 14 18    + 
      ((15/18 : ℚ) : ℝ) * cotangentTermV 15 18    + 
      ((10/18 : ℚ) : ℝ) * cotangentTermV 16 18    + 
      ((5/18 : ℚ) : ℝ) * cotangentTermV 17 18 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_18]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_49_18_lower : ℚ := 772279451199222629521 / 439804651110400000000
def cotangentSumVFormula_49_18_upper : ℚ := 48267466249709547569 / 27487790694400000000
theorem cotangentSumVFormula_49_18_bounds :
  ((cotangentSumVFormula_49_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 18 ∧
  cotangentSumVFormula 49 18 ≤ ((cotangentSumVFormula_49_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_18_unfold]
  have b_cot_1 := cot_pi_1_18_bounds
  simp only [cot_pi_1_18_lower, cot_pi_1_18_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_18_bounds
  simp only [cot_pi_2_18_lower, cot_pi_2_18_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_18_bounds
  simp only [cot_pi_3_18_lower, cot_pi_3_18_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_18_bounds
  simp only [cot_pi_4_18_lower, cot_pi_4_18_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_18_bounds
  simp only [cot_pi_5_18_lower, cot_pi_5_18_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_18_bounds
  simp only [cot_pi_6_18_lower, cot_pi_6_18_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_18_bounds
  simp only [cot_pi_7_18_lower, cot_pi_7_18_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_18_bounds
  simp only [cot_pi_8_18_lower, cot_pi_8_18_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_18_bounds
  simp only [cot_pi_9_18_lower, cot_pi_9_18_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_18_bounds
  simp only [cot_pi_10_18_lower, cot_pi_10_18_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_18_bounds
  simp only [cot_pi_11_18_lower, cot_pi_11_18_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_18_bounds
  simp only [cot_pi_12_18_lower, cot_pi_12_18_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_18_bounds
  simp only [cot_pi_13_18_lower, cot_pi_13_18_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_18_bounds
  simp only [cot_pi_14_18_lower, cot_pi_14_18_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_18_bounds
  simp only [cot_pi_15_18_lower, cot_pi_15_18_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_18_bounds
  simp only [cot_pi_16_18_lower, cot_pi_16_18_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_18_bounds
  simp only [cot_pi_17_18_lower, cot_pi_17_18_upper] at b_cot_17
  rw [cotangentSumVFormula_49_18_lower, cotangentSumVFormula_49_18_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1849_formula_bound :
  (((37228821141765610501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 18 49) ∧
  (vasyuninBEntryFormula 18 49 ≤ ((37231072941581108249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 18 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log18 := prim_log_18_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_18_49_bounds
  have b_Vkh := cotangentSumVFormula_49_18_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_18_49_lower, cotangentSumVFormula_18_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_18_lower, cotangentSumVFormula_49_18_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_49_unfold :
    cotangentSumVFormula 19 49 =
      ((19/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 19 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_19_49_lower : ℚ := -580643203440752787833 / 879609302220800000000
def cotangentSumVFormula_19_49_upper : ℚ := -580643185847903462167 / 879609302220800000000
theorem cotangentSumVFormula_19_49_bounds :
  ((cotangentSumVFormula_19_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 49 ∧
  cotangentSumVFormula 19 49 ≤ ((cotangentSumVFormula_19_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_49_unfold]
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
  rw [cotangentSumVFormula_19_49_lower, cotangentSumVFormula_19_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_19_unfold :
    cotangentSumVFormula 49 19 =
      ((11/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_49_19_lower : ℚ := -1148087209540891229457 / 3518437208883200000000
def cotangentSumVFormula_49_19_upper : ℚ := -1148087139171805645543 / 3518437208883200000000
theorem cotangentSumVFormula_49_19_bounds :
  ((cotangentSumVFormula_49_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 19 ∧
  cotangentSumVFormula 49 19 ≤ ((cotangentSumVFormula_49_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_19_unfold]
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
  rw [cotangentSumVFormula_49_19_lower, cotangentSumVFormula_49_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1949_formula_bound :
  (((36522576293697766751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 49) ∧
  (vasyuninBEntryFormula 19 49 ≤ ((36524828093513201999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_19_49_bounds
  have b_Vkh := cotangentSumVFormula_49_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_19_49_lower, cotangentSumVFormula_19_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_19_lower, cotangentSumVFormula_49_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_20_49_unfold :
    cotangentSumVFormula 20 49 =
      ((20/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 20 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_20_49_lower : ℚ := -3404246192570903622541 / 1759218604441600000000
def cotangentSumVFormula_20_49_upper : ℚ := -3404246157385237002459 / 1759218604441600000000
theorem cotangentSumVFormula_20_49_bounds :
  ((cotangentSumVFormula_20_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 49 ∧
  cotangentSumVFormula 20 49 ≤ ((cotangentSumVFormula_20_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_49_unfold]
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
  rw [cotangentSumVFormula_20_49_lower, cotangentSumVFormula_20_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_20_unfold :
    cotangentSumVFormula 49 20 =
      ((9/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_49_20_lower : ℚ := 2505487595497696377459 / 1759218604441600000000
def cotangentSumVFormula_49_20_upper : ℚ := 2505487630682284872541 / 1759218604441600000000
theorem cotangentSumVFormula_49_20_bounds :
  ((cotangentSumVFormula_49_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 20 ∧
  cotangentSumVFormula 49 20 ≤ ((cotangentSumVFormula_49_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_20_unfold]
  have b_cot_1 := cot_pi_1_20_bounds
  simp only [cot_pi_1_20_lower, cot_pi_1_20_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_20_bounds
  simp only [cot_pi_2_20_lower, cot_pi_2_20_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_20_bounds
  simp only [cot_pi_3_20_lower, cot_pi_3_20_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_20_bounds
  simp only [cot_pi_4_20_lower, cot_pi_4_20_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_20_bounds
  simp only [cot_pi_5_20_lower, cot_pi_5_20_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_20_bounds
  simp only [cot_pi_6_20_lower, cot_pi_6_20_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_20_bounds
  simp only [cot_pi_7_20_lower, cot_pi_7_20_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_20_bounds
  simp only [cot_pi_8_20_lower, cot_pi_8_20_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_20_bounds
  simp only [cot_pi_9_20_lower, cot_pi_9_20_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_20_bounds
  simp only [cot_pi_10_20_lower, cot_pi_10_20_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_20_bounds
  simp only [cot_pi_11_20_lower, cot_pi_11_20_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_20_bounds
  simp only [cot_pi_12_20_lower, cot_pi_12_20_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_20_bounds
  simp only [cot_pi_13_20_lower, cot_pi_13_20_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_20_bounds
  simp only [cot_pi_14_20_lower, cot_pi_14_20_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_20_bounds
  simp only [cot_pi_15_20_lower, cot_pi_15_20_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_20_bounds
  simp only [cot_pi_16_20_lower, cot_pi_16_20_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_20_bounds
  simp only [cot_pi_17_20_lower, cot_pi_17_20_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_20_bounds
  simp only [cot_pi_18_20_lower, cot_pi_18_20_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_20_bounds
  simp only [cot_pi_19_20_lower, cot_pi_19_20_upper] at b_cot_19
  rw [cotangentSumVFormula_49_20_lower, cotangentSumVFormula_49_20_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2049_formula_bound :
  (((35961080372033141751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 20 49) ∧
  (vasyuninBEntryFormula 20 49 ≤ ((35963332171848514499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 20 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log20 := prim_log_20_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_20_49_bounds
  have b_Vkh := cotangentSumVFormula_49_20_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_20_49_lower, cotangentSumVFormula_20_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_20_lower, cotangentSumVFormula_49_20_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_22_49_unfold :
    cotangentSumVFormula 22 49 =
      ((22/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 22 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_22_49_lower : ℚ := 716036070759463853823 / 219902325555200000000
def cotangentSumVFormula_22_49_upper : ℚ := 716036075157665052427 / 219902325555200000000
theorem cotangentSumVFormula_22_49_bounds :
  ((cotangentSumVFormula_22_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 22 49 ∧
  cotangentSumVFormula 22 49 ≤ ((cotangentSumVFormula_22_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_22_49_unfold]
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
  rw [cotangentSumVFormula_22_49_lower, cotangentSumVFormula_22_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_22_unfold :
    cotangentSumVFormula 49 22 =
      ((5/22 : ℚ) : ℝ) * cotangentTermV 1 22    + 
      ((10/22 : ℚ) : ℝ) * cotangentTermV 2 22    + 
      ((15/22 : ℚ) : ℝ) * cotangentTermV 3 22    + 
      ((20/22 : ℚ) : ℝ) * cotangentTermV 4 22    + 
      ((3/22 : ℚ) : ℝ) * cotangentTermV 5 22    + 
      ((8/22 : ℚ) : ℝ) * cotangentTermV 6 22    + 
      ((13/22 : ℚ) : ℝ) * cotangentTermV 7 22    + 
      ((18/22 : ℚ) : ℝ) * cotangentTermV 8 22    + 
      ((1/22 : ℚ) : ℝ) * cotangentTermV 9 22    + 
      ((6/22 : ℚ) : ℝ) * cotangentTermV 10 22    + 
      ((11/22 : ℚ) : ℝ) * cotangentTermV 11 22    + 
      ((16/22 : ℚ) : ℝ) * cotangentTermV 12 22    + 
      ((21/22 : ℚ) : ℝ) * cotangentTermV 13 22    + 
      ((4/22 : ℚ) : ℝ) * cotangentTermV 14 22    + 
      ((9/22 : ℚ) : ℝ) * cotangentTermV 15 22    + 
      ((14/22 : ℚ) : ℝ) * cotangentTermV 16 22    + 
      ((19/22 : ℚ) : ℝ) * cotangentTermV 17 22    + 
      ((2/22 : ℚ) : ℝ) * cotangentTermV 18 22    + 
      ((7/22 : ℚ) : ℝ) * cotangentTermV 19 22    + 
      ((12/22 : ℚ) : ℝ) * cotangentTermV 20 22    + 
      ((17/22 : ℚ) : ℝ) * cotangentTermV 21 22 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_22]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((5/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((10/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((15/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((20/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((3/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((8/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((13/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((18/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((1/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((6/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((11/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((16/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((21/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((4/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((9/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((14/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((19/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((2/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((7/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((12/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((17/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21]
  try ring

def cotangentSumVFormula_49_22_lower : ℚ := -667275632728540833677 / 219902325555200000000
def cotangentSumVFormula_49_22_upper : ℚ := -667275628330454478823 / 219902325555200000000
theorem cotangentSumVFormula_49_22_bounds :
  ((cotangentSumVFormula_49_22_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 22 ∧
  cotangentSumVFormula 49 22 ≤ ((cotangentSumVFormula_49_22_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_22_unfold]
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
  rw [cotangentSumVFormula_49_22_lower, cotangentSumVFormula_49_22_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2249_formula_bound :
  (((140345188342122676379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 22 49) ∧
  (vasyuninBEntryFormula 22 49 ≤ ((140354195541383729871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 22 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log22 := prim_log_22_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_22_49_bounds
  have b_Vkh := cotangentSumVFormula_49_22_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_22_lower, prim_log_22_upper] at b_log22
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_22_49_lower, cotangentSumVFormula_22_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_22_lower, cotangentSumVFormula_49_22_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_49_unfold :
    cotangentSumVFormula 23 49 =
      ((23/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 23 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_23_49_lower : ℚ := 3170910593062624192021 / 439804651110400000000
def cotangentSumVFormula_23_49_upper : ℚ := 3170910601859013307979 / 439804651110400000000
theorem cotangentSumVFormula_23_49_bounds :
  ((cotangentSumVFormula_23_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 49 ∧
  cotangentSumVFormula 23 49 ≤ ((cotangentSumVFormula_23_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_49_unfold]
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
  rw [cotangentSumVFormula_23_49_lower, cotangentSumVFormula_23_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_23_unfold :
    cotangentSumVFormula 49 23 =
      ((3/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_49_23_lower : ℚ := -3001020479209432057979 / 439804651110400000000
def cotangentSumVFormula_49_23_upper : ℚ := -3001020470413243723271 / 439804651110400000000
theorem cotangentSumVFormula_49_23_bounds :
  ((cotangentSumVFormula_49_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 23 ∧
  cotangentSumVFormula 49 23 ≤ ((cotangentSumVFormula_49_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_23_unfold]
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
  rw [cotangentSumVFormula_49_23_lower, cotangentSumVFormula_49_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2349_formula_bound :
  (((139638237103617770129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 49) ∧
  (vasyuninBEntryFormula 23 49 ≤ ((139647244302878604871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_23_49_bounds
  have b_Vkh := cotangentSumVFormula_49_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_23_49_lower, cotangentSumVFormula_23_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_23_lower, cotangentSumVFormula_49_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_24_49_unfold :
    cotangentSumVFormula 24 49 =
      ((24/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 24 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_24_49_lower : ℚ := 3359333371404077916323 / 219902325555200000000
def cotangentSumVFormula_24_49_upper : ℚ := 3359333375802297083677 / 219902325555200000000
theorem cotangentSumVFormula_24_49_bounds :
  ((cotangentSumVFormula_24_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 24 49 ∧
  cotangentSumVFormula 24 49 ≤ ((cotangentSumVFormula_24_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_24_49_unfold]
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
  rw [cotangentSumVFormula_24_49_lower, cotangentSumVFormula_24_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_24_unfold :
    cotangentSumVFormula 49 24 =
      ((1/24 : ℚ) : ℝ) * cotangentTermV 1 24    + 
      ((2/24 : ℚ) : ℝ) * cotangentTermV 2 24    + 
      ((3/24 : ℚ) : ℝ) * cotangentTermV 3 24    + 
      ((4/24 : ℚ) : ℝ) * cotangentTermV 4 24    + 
      ((5/24 : ℚ) : ℝ) * cotangentTermV 5 24    + 
      ((6/24 : ℚ) : ℝ) * cotangentTermV 6 24    + 
      ((7/24 : ℚ) : ℝ) * cotangentTermV 7 24    + 
      ((8/24 : ℚ) : ℝ) * cotangentTermV 8 24    + 
      ((9/24 : ℚ) : ℝ) * cotangentTermV 9 24    + 
      ((10/24 : ℚ) : ℝ) * cotangentTermV 10 24    + 
      ((11/24 : ℚ) : ℝ) * cotangentTermV 11 24    + 
      ((12/24 : ℚ) : ℝ) * cotangentTermV 12 24    + 
      ((13/24 : ℚ) : ℝ) * cotangentTermV 13 24    + 
      ((14/24 : ℚ) : ℝ) * cotangentTermV 14 24    + 
      ((15/24 : ℚ) : ℝ) * cotangentTermV 15 24    + 
      ((16/24 : ℚ) : ℝ) * cotangentTermV 16 24    + 
      ((17/24 : ℚ) : ℝ) * cotangentTermV 17 24    + 
      ((18/24 : ℚ) : ℝ) * cotangentTermV 18 24    + 
      ((19/24 : ℚ) : ℝ) * cotangentTermV 19 24    + 
      ((20/24 : ℚ) : ℝ) * cotangentTermV 20 24    + 
      ((21/24 : ℚ) : ℝ) * cotangentTermV 21 24    + 
      ((22/24 : ℚ) : ℝ) * cotangentTermV 22 24    + 
      ((23/24 : ℚ) : ℝ) * cotangentTermV 23 24 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_24]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((1/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((2/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((3/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((4/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((5/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((6/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((7/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((8/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((9/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((10/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((11/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((12/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((13/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((14/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((15/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((16/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((17/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((18/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((19/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((20/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((21/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((22/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((23/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23]
  try ring

def cotangentSumVFormula_49_24_lower : ℚ := -411485210788633766319 / 27487790694400000000
def cotangentSumVFormula_49_24_upper : ℚ := -205742605119435655903 / 13743895347200000000
theorem cotangentSumVFormula_49_24_bounds :
  ((cotangentSumVFormula_49_24_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 24 ∧
  cotangentSumVFormula 49 24 ≤ ((cotangentSumVFormula_49_24_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_24_unfold]
  have b_cot_1 := cot_pi_1_24_bounds
  simp only [cot_pi_1_24_lower, cot_pi_1_24_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_24_bounds
  simp only [cot_pi_2_24_lower, cot_pi_2_24_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_24_bounds
  simp only [cot_pi_3_24_lower, cot_pi_3_24_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_24_bounds
  simp only [cot_pi_4_24_lower, cot_pi_4_24_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_24_bounds
  simp only [cot_pi_5_24_lower, cot_pi_5_24_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_24_bounds
  simp only [cot_pi_6_24_lower, cot_pi_6_24_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_24_bounds
  simp only [cot_pi_7_24_lower, cot_pi_7_24_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_24_bounds
  simp only [cot_pi_8_24_lower, cot_pi_8_24_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_24_bounds
  simp only [cot_pi_9_24_lower, cot_pi_9_24_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_24_bounds
  simp only [cot_pi_10_24_lower, cot_pi_10_24_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_24_bounds
  simp only [cot_pi_11_24_lower, cot_pi_11_24_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_24_bounds
  simp only [cot_pi_12_24_lower, cot_pi_12_24_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_24_bounds
  simp only [cot_pi_13_24_lower, cot_pi_13_24_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_24_bounds
  simp only [cot_pi_14_24_lower, cot_pi_14_24_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_24_bounds
  simp only [cot_pi_15_24_lower, cot_pi_15_24_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_24_bounds
  simp only [cot_pi_16_24_lower, cot_pi_16_24_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_24_bounds
  simp only [cot_pi_17_24_lower, cot_pi_17_24_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_24_bounds
  simp only [cot_pi_18_24_lower, cot_pi_18_24_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_24_bounds
  simp only [cot_pi_19_24_lower, cot_pi_19_24_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_24_bounds
  simp only [cot_pi_20_24_lower, cot_pi_20_24_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_24_bounds
  simp only [cot_pi_21_24_lower, cot_pi_21_24_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_24_bounds
  simp only [cot_pi_22_24_lower, cot_pi_22_24_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_24_bounds
  simp only [cot_pi_23_24_lower, cot_pi_23_24_upper] at b_cot_23
  rw [cotangentSumVFormula_49_24_lower, cotangentSumVFormula_49_24_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2449_formula_bound :
  (((140197770451352645129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 24 49) ∧
  (vasyuninBEntryFormula 24 49 ≤ ((140206777650614011121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 24 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log24 := prim_log_24_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_24_49_bounds
  have b_Vkh := cotangentSumVFormula_49_24_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_24_lower, prim_log_24_upper] at b_log24
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_24_49_lower, cotangentSumVFormula_24_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_24_lower, cotangentSumVFormula_49_24_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_25_49_unfold :
    cotangentSumVFormula 25 49 =
      ((25/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 25 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_25_49_lower : ℚ := -52489583996910910243 / 3435973836800000000
def cotangentSumVFormula_25_49_upper : ℚ := -1679666685702042669099 / 109951162777600000000
theorem cotangentSumVFormula_25_49_bounds :
  ((cotangentSumVFormula_25_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 49 ∧
  cotangentSumVFormula 25 49 ≤ ((cotangentSumVFormula_25_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_49_unfold]
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
  rw [cotangentSumVFormula_25_49_lower, cotangentSumVFormula_25_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_25_unfold :
    cotangentSumVFormula 49 25 =
      ((24/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((22/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((21/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((19/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((17/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((14/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((12/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((11/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_49_25_lower : ℚ := 3497497102962137291323 / 219902325555200000000
def cotangentSumVFormula_49_25_upper : ℚ := 3497497107360229114927 / 219902325555200000000
theorem cotangentSumVFormula_49_25_bounds :
  ((cotangentSumVFormula_49_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 25 ∧
  cotangentSumVFormula 49 25 ≤ ((cotangentSumVFormula_49_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_25_unfold]
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
  rw [cotangentSumVFormula_49_25_lower, cotangentSumVFormula_49_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2549_formula_bound :
  (((138163040630143488879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 49) ∧
  (vasyuninBEntryFormula 25 49 ≤ ((138172047829404261121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_25_49_bounds
  have b_Vkh := cotangentSumVFormula_49_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_25_49_lower, cotangentSumVFormula_25_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_25_lower, cotangentSumVFormula_49_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_26_49_unfold :
    cotangentSumVFormula 26 49 =
      ((26/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 26 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_26_49_lower : ℚ := -792727650464754987151 / 109951162777600000000
def cotangentSumVFormula_26_49_upper : ℚ := -1585455296531293541323 / 219902325555200000000
theorem cotangentSumVFormula_26_49_bounds :
  ((cotangentSumVFormula_26_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 26 49 ∧
  cotangentSumVFormula 26 49 ≤ ((cotangentSumVFormula_26_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_26_49_unfold]
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
  rw [cotangentSumVFormula_26_49_lower, cotangentSumVFormula_26_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_26_unfold :
    cotangentSumVFormula 49 26 =
      ((23/26 : ℚ) : ℝ) * cotangentTermV 1 26    + 
      ((20/26 : ℚ) : ℝ) * cotangentTermV 2 26    + 
      ((17/26 : ℚ) : ℝ) * cotangentTermV 3 26    + 
      ((14/26 : ℚ) : ℝ) * cotangentTermV 4 26    + 
      ((11/26 : ℚ) : ℝ) * cotangentTermV 5 26    + 
      ((8/26 : ℚ) : ℝ) * cotangentTermV 6 26    + 
      ((5/26 : ℚ) : ℝ) * cotangentTermV 7 26    + 
      ((2/26 : ℚ) : ℝ) * cotangentTermV 8 26    + 
      ((25/26 : ℚ) : ℝ) * cotangentTermV 9 26    + 
      ((22/26 : ℚ) : ℝ) * cotangentTermV 10 26    + 
      ((19/26 : ℚ) : ℝ) * cotangentTermV 11 26    + 
      ((16/26 : ℚ) : ℝ) * cotangentTermV 12 26    + 
      ((13/26 : ℚ) : ℝ) * cotangentTermV 13 26    + 
      ((10/26 : ℚ) : ℝ) * cotangentTermV 14 26    + 
      ((7/26 : ℚ) : ℝ) * cotangentTermV 15 26    + 
      ((4/26 : ℚ) : ℝ) * cotangentTermV 16 26    + 
      ((1/26 : ℚ) : ℝ) * cotangentTermV 17 26    + 
      ((24/26 : ℚ) : ℝ) * cotangentTermV 18 26    + 
      ((21/26 : ℚ) : ℝ) * cotangentTermV 19 26    + 
      ((18/26 : ℚ) : ℝ) * cotangentTermV 20 26    + 
      ((15/26 : ℚ) : ℝ) * cotangentTermV 21 26    + 
      ((12/26 : ℚ) : ℝ) * cotangentTermV 22 26    + 
      ((9/26 : ℚ) : ℝ) * cotangentTermV 23 26    + 
      ((6/26 : ℚ) : ℝ) * cotangentTermV 24 26    + 
      ((3/26 : ℚ) : ℝ) * cotangentTermV 25 26 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_26]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((23/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((20/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((17/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((14/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((11/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((8/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((5/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((2/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((25/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((22/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((19/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((16/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((13/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((10/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((7/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((4/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((1/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((24/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((21/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((18/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((15/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((12/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((9/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((6/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((3/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25]
  try ring

def cotangentSumVFormula_49_26_lower : ℚ := 1886812728814737291323 / 219902325555200000000
def cotangentSumVFormula_49_26_upper : ℚ := 1886812733212819739927 / 219902325555200000000
theorem cotangentSumVFormula_49_26_bounds :
  ((cotangentSumVFormula_49_26_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 26 ∧
  cotangentSumVFormula 49 26 ≤ ((cotangentSumVFormula_49_26_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_26_unfold]
  have b_cot_1 := cot_pi_1_26_bounds
  simp only [cot_pi_1_26_lower, cot_pi_1_26_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_26_bounds
  simp only [cot_pi_2_26_lower, cot_pi_2_26_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_26_bounds
  simp only [cot_pi_3_26_lower, cot_pi_3_26_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_26_bounds
  simp only [cot_pi_4_26_lower, cot_pi_4_26_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_26_bounds
  simp only [cot_pi_5_26_lower, cot_pi_5_26_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_26_bounds
  simp only [cot_pi_6_26_lower, cot_pi_6_26_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_26_bounds
  simp only [cot_pi_7_26_lower, cot_pi_7_26_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_26_bounds
  simp only [cot_pi_8_26_lower, cot_pi_8_26_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_26_bounds
  simp only [cot_pi_9_26_lower, cot_pi_9_26_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_26_bounds
  simp only [cot_pi_10_26_lower, cot_pi_10_26_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_26_bounds
  simp only [cot_pi_11_26_lower, cot_pi_11_26_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_26_bounds
  simp only [cot_pi_12_26_lower, cot_pi_12_26_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_26_bounds
  simp only [cot_pi_13_26_lower, cot_pi_13_26_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_26_bounds
  simp only [cot_pi_14_26_lower, cot_pi_14_26_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_26_bounds
  simp only [cot_pi_15_26_lower, cot_pi_15_26_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_26_bounds
  simp only [cot_pi_16_26_lower, cot_pi_16_26_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_26_bounds
  simp only [cot_pi_17_26_lower, cot_pi_17_26_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_26_bounds
  simp only [cot_pi_18_26_lower, cot_pi_18_26_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_26_bounds
  simp only [cot_pi_19_26_lower, cot_pi_19_26_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_26_bounds
  simp only [cot_pi_20_26_lower, cot_pi_20_26_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_26_bounds
  simp only [cot_pi_21_26_lower, cot_pi_21_26_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_26_bounds
  simp only [cot_pi_22_26_lower, cot_pi_22_26_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_26_bounds
  simp only [cot_pi_23_26_lower, cot_pi_23_26_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_26_bounds
  simp only [cot_pi_24_26_lower, cot_pi_24_26_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_26_bounds
  simp only [cot_pi_25_26_lower, cot_pi_25_26_upper] at b_cot_25
  rw [cotangentSumVFormula_49_26_lower, cotangentSumVFormula_49_26_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2649_formula_bound :
  (((66870081026122236627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 26 49) ∧
  (vasyuninBEntryFormula 26 49 ≤ ((4179661539109527203 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 26 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log26 := prim_log_26_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_26_49_bounds
  have b_Vkh := cotangentSumVFormula_49_26_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_26_lower, prim_log_26_upper] at b_log26
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_26_49_lower, cotangentSumVFormula_26_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_26_lower, cotangentSumVFormula_49_26_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_27_49_unfold :
    cotangentSumVFormula 27 49 =
      ((27/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 27 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_27_49_lower : ℚ := -358018037578832330901 / 109951162777600000000
def cotangentSumVFormula_27_49_upper : ℚ := -716036070759452135073 / 219902325555200000000
theorem cotangentSumVFormula_27_49_bounds :
  ((cotangentSumVFormula_27_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 27 49 ∧
  cotangentSumVFormula 27 49 ≤ ((cotangentSumVFormula_27_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_27_49_unfold]
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
  rw [cotangentSumVFormula_27_49_lower, cotangentSumVFormula_27_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_27_unfold :
    cotangentSumVFormula 49 27 =
      ((22/27 : ℚ) : ℝ) * cotangentTermV 1 27    + 
      ((17/27 : ℚ) : ℝ) * cotangentTermV 2 27    + 
      ((12/27 : ℚ) : ℝ) * cotangentTermV 3 27    + 
      ((7/27 : ℚ) : ℝ) * cotangentTermV 4 27    + 
      ((2/27 : ℚ) : ℝ) * cotangentTermV 5 27    + 
      ((24/27 : ℚ) : ℝ) * cotangentTermV 6 27    + 
      ((19/27 : ℚ) : ℝ) * cotangentTermV 7 27    + 
      ((14/27 : ℚ) : ℝ) * cotangentTermV 8 27    + 
      ((9/27 : ℚ) : ℝ) * cotangentTermV 9 27    + 
      ((4/27 : ℚ) : ℝ) * cotangentTermV 10 27    + 
      ((26/27 : ℚ) : ℝ) * cotangentTermV 11 27    + 
      ((21/27 : ℚ) : ℝ) * cotangentTermV 12 27    + 
      ((16/27 : ℚ) : ℝ) * cotangentTermV 13 27    + 
      ((11/27 : ℚ) : ℝ) * cotangentTermV 14 27    + 
      ((6/27 : ℚ) : ℝ) * cotangentTermV 15 27    + 
      ((1/27 : ℚ) : ℝ) * cotangentTermV 16 27    + 
      ((23/27 : ℚ) : ℝ) * cotangentTermV 17 27    + 
      ((18/27 : ℚ) : ℝ) * cotangentTermV 18 27    + 
      ((13/27 : ℚ) : ℝ) * cotangentTermV 19 27    + 
      ((8/27 : ℚ) : ℝ) * cotangentTermV 20 27    + 
      ((3/27 : ℚ) : ℝ) * cotangentTermV 21 27    + 
      ((25/27 : ℚ) : ℝ) * cotangentTermV 22 27    + 
      ((20/27 : ℚ) : ℝ) * cotangentTermV 23 27    + 
      ((15/27 : ℚ) : ℝ) * cotangentTermV 24 27    + 
      ((10/27 : ℚ) : ℝ) * cotangentTermV 25 27    + 
      ((5/27 : ℚ) : ℝ) * cotangentTermV 26 27 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_27]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((22/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((17/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((12/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((7/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((2/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((24/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((19/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((14/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((9/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((4/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((26/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((21/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((16/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((11/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((6/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((1/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((23/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((18/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((13/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((8/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((3/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((25/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((20/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((15/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((10/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((5/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26]
  try ring

def cotangentSumVFormula_49_27_lower : ℚ := 1132580020484146666323 / 219902325555200000000
def cotangentSumVFormula_49_27_upper : ℚ := 566290012441116705901 / 109951162777600000000
theorem cotangentSumVFormula_49_27_bounds :
  ((cotangentSumVFormula_49_27_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 27 ∧
  cotangentSumVFormula 49 27 ≤ ((cotangentSumVFormula_49_27_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_27_unfold]
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
  rw [cotangentSumVFormula_49_27_lower, cotangentSumVFormula_49_27_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2749_formula_bound :
  (((65311648817693549127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 27 49) ∧
  (vasyuninBEntryFormula 27 49 ≤ ((32658076208661826999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 27 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log27 := prim_log_27_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_27_49_bounds
  have b_Vkh := cotangentSumVFormula_49_27_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_27_lower, prim_log_27_upper] at b_log27
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_27_49_lower, cotangentSumVFormula_27_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_27_lower, cotangentSumVFormula_49_27_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_49_unfold :
    cotangentSumVFormula 29 49 =
      ((29/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 29 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_29_49_lower : ℚ := 851061539346317942021 / 439804651110400000000
def cotangentSumVFormula_29_49_upper : ℚ := 851061548142735964229 / 439804651110400000000
theorem cotangentSumVFormula_29_49_bounds :
  ((cotangentSumVFormula_29_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 49 ∧
  cotangentSumVFormula 29 49 ≤ ((cotangentSumVFormula_29_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_49_unfold]
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
  rw [cotangentSumVFormula_29_49_lower, cotangentSumVFormula_29_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_29_unfold :
    cotangentSumVFormula 49 29 =
      ((20/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_49_29_lower : ℚ := 2405604321810662676793 / 3518437208883200000000
def cotangentSumVFormula_49_29_upper : ℚ := 2405604392180227948207 / 3518437208883200000000
theorem cotangentSumVFormula_49_29_bounds :
  ((cotangentSumVFormula_49_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 29 ∧
  cotangentSumVFormula 49 29 ≤ ((cotangentSumVFormula_49_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_29_unfold]
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
  rw [cotangentSumVFormula_49_29_lower, cotangentSumVFormula_49_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2949_formula_bound :
  (((126156321071365395129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 49) ∧
  (vasyuninBEntryFormula 29 49 ≤ ((126165328270625386121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_29_49_bounds
  have b_Vkh := cotangentSumVFormula_49_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_29_49_lower, cotangentSumVFormula_29_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_29_lower, cotangentSumVFormula_49_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_30_49_unfold :
    cotangentSumVFormula 30 49 =
      ((30/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 30 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_30_49_lower : ℚ := 2322572743391765801793 / 3518437208883200000000
def cotangentSumVFormula_30_49_upper : ℚ := 2322572813763090448207 / 3518437208883200000000
theorem cotangentSumVFormula_30_49_bounds :
  ((cotangentSumVFormula_30_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 30 49 ∧
  cotangentSumVFormula 30 49 ≤ ((cotangentSumVFormula_30_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_30_49_unfold]
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
  rw [cotangentSumVFormula_30_49_lower, cotangentSumVFormula_30_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_30_unfold :
    cotangentSumVFormula 49 30 =
      ((19/30 : ℚ) : ℝ) * cotangentTermV 1 30    + 
      ((8/30 : ℚ) : ℝ) * cotangentTermV 2 30    + 
      ((27/30 : ℚ) : ℝ) * cotangentTermV 3 30    + 
      ((16/30 : ℚ) : ℝ) * cotangentTermV 4 30    + 
      ((5/30 : ℚ) : ℝ) * cotangentTermV 5 30    + 
      ((24/30 : ℚ) : ℝ) * cotangentTermV 6 30    + 
      ((13/30 : ℚ) : ℝ) * cotangentTermV 7 30    + 
      ((2/30 : ℚ) : ℝ) * cotangentTermV 8 30    + 
      ((21/30 : ℚ) : ℝ) * cotangentTermV 9 30    + 
      ((10/30 : ℚ) : ℝ) * cotangentTermV 10 30    + 
      ((29/30 : ℚ) : ℝ) * cotangentTermV 11 30    + 
      ((18/30 : ℚ) : ℝ) * cotangentTermV 12 30    + 
      ((7/30 : ℚ) : ℝ) * cotangentTermV 13 30    + 
      ((26/30 : ℚ) : ℝ) * cotangentTermV 14 30    + 
      ((15/30 : ℚ) : ℝ) * cotangentTermV 15 30    + 
      ((4/30 : ℚ) : ℝ) * cotangentTermV 16 30    + 
      ((23/30 : ℚ) : ℝ) * cotangentTermV 17 30    + 
      ((12/30 : ℚ) : ℝ) * cotangentTermV 18 30    + 
      ((1/30 : ℚ) : ℝ) * cotangentTermV 19 30    + 
      ((20/30 : ℚ) : ℝ) * cotangentTermV 20 30    + 
      ((9/30 : ℚ) : ℝ) * cotangentTermV 21 30    + 
      ((28/30 : ℚ) : ℝ) * cotangentTermV 22 30    + 
      ((17/30 : ℚ) : ℝ) * cotangentTermV 23 30    + 
      ((6/30 : ℚ) : ℝ) * cotangentTermV 24 30    + 
      ((25/30 : ℚ) : ℝ) * cotangentTermV 25 30    + 
      ((14/30 : ℚ) : ℝ) * cotangentTermV 26 30    + 
      ((3/30 : ℚ) : ℝ) * cotangentTermV 27 30    + 
      ((22/30 : ℚ) : ℝ) * cotangentTermV 28 30    + 
      ((11/30 : ℚ) : ℝ) * cotangentTermV 29 30 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_30]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((19/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((8/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((27/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((16/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((5/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((24/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((13/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((2/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((21/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((10/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((29/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((18/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((7/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((26/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((15/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((4/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((23/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((12/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((1/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((20/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((9/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((28/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((17/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((6/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((25/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((14/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((3/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((22/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((11/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29]
  try ring

def cotangentSumVFormula_49_30_lower : ℚ := 1969145944901705024667 / 879609302220800000000
def cotangentSumVFormula_49_30_upper : ℚ := 1969145962494120756583 / 879609302220800000000
theorem cotangentSumVFormula_49_30_bounds :
  ((cotangentSumVFormula_49_30_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 30 ∧
  cotangentSumVFormula 49 30 ≤ ((cotangentSumVFormula_49_30_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_30_unfold]
  have b_cot_1 := cot_pi_1_30_bounds
  simp only [cot_pi_1_30_lower, cot_pi_1_30_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_30_bounds
  simp only [cot_pi_2_30_lower, cot_pi_2_30_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_30_bounds
  simp only [cot_pi_3_30_lower, cot_pi_3_30_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_30_bounds
  simp only [cot_pi_4_30_lower, cot_pi_4_30_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_30_bounds
  simp only [cot_pi_5_30_lower, cot_pi_5_30_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_30_bounds
  simp only [cot_pi_6_30_lower, cot_pi_6_30_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_30_bounds
  simp only [cot_pi_7_30_lower, cot_pi_7_30_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_30_bounds
  simp only [cot_pi_8_30_lower, cot_pi_8_30_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_30_bounds
  simp only [cot_pi_9_30_lower, cot_pi_9_30_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_30_bounds
  simp only [cot_pi_10_30_lower, cot_pi_10_30_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_30_bounds
  simp only [cot_pi_11_30_lower, cot_pi_11_30_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_30_bounds
  simp only [cot_pi_12_30_lower, cot_pi_12_30_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_30_bounds
  simp only [cot_pi_13_30_lower, cot_pi_13_30_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_30_bounds
  simp only [cot_pi_14_30_lower, cot_pi_14_30_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_30_bounds
  simp only [cot_pi_15_30_lower, cot_pi_15_30_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_30_bounds
  simp only [cot_pi_16_30_lower, cot_pi_16_30_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_30_bounds
  simp only [cot_pi_17_30_lower, cot_pi_17_30_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_30_bounds
  simp only [cot_pi_18_30_lower, cot_pi_18_30_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_30_bounds
  simp only [cot_pi_19_30_lower, cot_pi_19_30_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_30_bounds
  simp only [cot_pi_20_30_lower, cot_pi_20_30_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_30_bounds
  simp only [cot_pi_21_30_lower, cot_pi_21_30_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_30_bounds
  simp only [cot_pi_22_30_lower, cot_pi_22_30_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_30_bounds
  simp only [cot_pi_23_30_lower, cot_pi_23_30_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_30_bounds
  simp only [cot_pi_24_30_lower, cot_pi_24_30_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_30_bounds
  simp only [cot_pi_25_30_lower, cot_pi_25_30_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_30_bounds
  simp only [cot_pi_26_30_lower, cot_pi_26_30_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_30_bounds
  simp only [cot_pi_27_30_lower, cot_pi_27_30_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_30_bounds
  simp only [cot_pi_28_30_lower, cot_pi_28_30_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_30_bounds
  simp only [cot_pi_29_30_lower, cot_pi_29_30_upper] at b_cot_29
  rw [cotangentSumVFormula_49_30_lower, cotangentSumVFormula_49_30_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3049_formula_bound :
  (((62162470409605955377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 30 49) ∧
  (vasyuninBEntryFormula 30 49 ≤ ((62166974009235919623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 30 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log30 := prim_log_30_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_30_49_bounds
  have b_Vkh := cotangentSumVFormula_49_30_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_30_lower, prim_log_30_upper] at b_log30
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_30_49_lower, cotangentSumVFormula_30_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_30_lower, cotangentSumVFormula_49_30_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_49_unfold :
    cotangentSumVFormula 31 49 =
      ((31/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 31 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_31_49_lower : ℚ := 2919438472014983149667 / 879609302220800000000
def cotangentSumVFormula_31_49_upper : ℚ := 2919438489607790287833 / 879609302220800000000
theorem cotangentSumVFormula_31_49_bounds :
  ((cotangentSumVFormula_31_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 49 ∧
  cotangentSumVFormula 31 49 ≤ ((cotangentSumVFormula_31_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_49_unfold]
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
  rw [cotangentSumVFormula_31_49_lower, cotangentSumVFormula_31_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_31_unfold :
    cotangentSumVFormula 49 31 =
      ((18/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_49_31_lower : ℚ := -5525111839111110069 / 27487790694400000000
def cotangentSumVFormula_49_31_upper : ℚ := -44200890314775572573 / 219902325555200000000
theorem cotangentSumVFormula_49_31_bounds :
  ((cotangentSumVFormula_49_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 31 ∧
  cotangentSumVFormula 49 31 ≤ ((cotangentSumVFormula_49_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_31_unfold]
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
  rw [cotangentSumVFormula_49_31_lower, cotangentSumVFormula_49_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3149_formula_bound :
  (((122764368984431770129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 49) ∧
  (vasyuninBEntryFormula 31 49 ≤ ((122773376183691573621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_31_49_bounds
  have b_Vkh := cotangentSumVFormula_49_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_31_49_lower, cotangentSumVFormula_31_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_31_lower, cotangentSumVFormula_49_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_32_49_unfold :
    cotangentSumVFormula 32 49 =
      ((32/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 32 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_32_49_lower : ℚ := 1696984420138699791323 / 219902325555200000000
def cotangentSumVFormula_32_49_upper : ℚ := 848492212268447955901 / 109951162777600000000
theorem cotangentSumVFormula_32_49_bounds :
  ((cotangentSumVFormula_32_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 32 49 ∧
  cotangentSumVFormula 32 49 ≤ ((cotangentSumVFormula_32_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_32_49_unfold]
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
  rw [cotangentSumVFormula_32_49_lower, cotangentSumVFormula_32_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_32_unfold :
    cotangentSumVFormula 49 32 =
      ((17/32 : ℚ) : ℝ) * cotangentTermV 1 32    + 
      ((2/32 : ℚ) : ℝ) * cotangentTermV 2 32    + 
      ((19/32 : ℚ) : ℝ) * cotangentTermV 3 32    + 
      ((4/32 : ℚ) : ℝ) * cotangentTermV 4 32    + 
      ((21/32 : ℚ) : ℝ) * cotangentTermV 5 32    + 
      ((6/32 : ℚ) : ℝ) * cotangentTermV 6 32    + 
      ((23/32 : ℚ) : ℝ) * cotangentTermV 7 32    + 
      ((8/32 : ℚ) : ℝ) * cotangentTermV 8 32    + 
      ((25/32 : ℚ) : ℝ) * cotangentTermV 9 32    + 
      ((10/32 : ℚ) : ℝ) * cotangentTermV 10 32    + 
      ((27/32 : ℚ) : ℝ) * cotangentTermV 11 32    + 
      ((12/32 : ℚ) : ℝ) * cotangentTermV 12 32    + 
      ((29/32 : ℚ) : ℝ) * cotangentTermV 13 32    + 
      ((14/32 : ℚ) : ℝ) * cotangentTermV 14 32    + 
      ((31/32 : ℚ) : ℝ) * cotangentTermV 15 32    + 
      ((16/32 : ℚ) : ℝ) * cotangentTermV 16 32    + 
      ((1/32 : ℚ) : ℝ) * cotangentTermV 17 32    + 
      ((18/32 : ℚ) : ℝ) * cotangentTermV 18 32    + 
      ((3/32 : ℚ) : ℝ) * cotangentTermV 19 32    + 
      ((20/32 : ℚ) : ℝ) * cotangentTermV 20 32    + 
      ((5/32 : ℚ) : ℝ) * cotangentTermV 21 32    + 
      ((22/32 : ℚ) : ℝ) * cotangentTermV 22 32    + 
      ((7/32 : ℚ) : ℝ) * cotangentTermV 23 32    + 
      ((24/32 : ℚ) : ℝ) * cotangentTermV 24 32    + 
      ((9/32 : ℚ) : ℝ) * cotangentTermV 25 32    + 
      ((26/32 : ℚ) : ℝ) * cotangentTermV 26 32    + 
      ((11/32 : ℚ) : ℝ) * cotangentTermV 27 32    + 
      ((28/32 : ℚ) : ℝ) * cotangentTermV 28 32    + 
      ((13/32 : ℚ) : ℝ) * cotangentTermV 29 32    + 
      ((30/32 : ℚ) : ℝ) * cotangentTermV 30 32    + 
      ((15/32 : ℚ) : ℝ) * cotangentTermV 31 32 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_32]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((17/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((2/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((19/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((4/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((21/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((6/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((23/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((8/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((25/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((10/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((27/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((12/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((29/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((14/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((31/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((16/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((1/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((18/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((3/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((20/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((5/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((22/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((7/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((24/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((9/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((26/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((11/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((28/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((13/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((30/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((15/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31]
  try ring

def cotangentSumVFormula_49_32_lower : ℚ := -1972793321228317995479 / 439804651110400000000
def cotangentSumVFormula_49_32_upper : ℚ := -1972793312432121848271 / 439804651110400000000
theorem cotangentSumVFormula_49_32_bounds :
  ((cotangentSumVFormula_49_32_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 32 ∧
  cotangentSumVFormula 49 32 ≤ ((cotangentSumVFormula_49_32_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_32_unfold]
  have b_cot_1 := cot_pi_1_32_bounds
  simp only [cot_pi_1_32_lower, cot_pi_1_32_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_32_bounds
  simp only [cot_pi_2_32_lower, cot_pi_2_32_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_32_bounds
  simp only [cot_pi_3_32_lower, cot_pi_3_32_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_32_bounds
  simp only [cot_pi_4_32_lower, cot_pi_4_32_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_32_bounds
  simp only [cot_pi_5_32_lower, cot_pi_5_32_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_32_bounds
  simp only [cot_pi_6_32_lower, cot_pi_6_32_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_32_bounds
  simp only [cot_pi_7_32_lower, cot_pi_7_32_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_32_bounds
  simp only [cot_pi_8_32_lower, cot_pi_8_32_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_32_bounds
  simp only [cot_pi_9_32_lower, cot_pi_9_32_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_32_bounds
  simp only [cot_pi_10_32_lower, cot_pi_10_32_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_32_bounds
  simp only [cot_pi_11_32_lower, cot_pi_11_32_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_32_bounds
  simp only [cot_pi_12_32_lower, cot_pi_12_32_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_32_bounds
  simp only [cot_pi_13_32_lower, cot_pi_13_32_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_32_bounds
  simp only [cot_pi_14_32_lower, cot_pi_14_32_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_32_bounds
  simp only [cot_pi_15_32_lower, cot_pi_15_32_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_32_bounds
  simp only [cot_pi_16_32_lower, cot_pi_16_32_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_32_bounds
  simp only [cot_pi_17_32_lower, cot_pi_17_32_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_32_bounds
  simp only [cot_pi_18_32_lower, cot_pi_18_32_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_32_bounds
  simp only [cot_pi_19_32_lower, cot_pi_19_32_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_32_bounds
  simp only [cot_pi_20_32_lower, cot_pi_20_32_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_32_bounds
  simp only [cot_pi_21_32_lower, cot_pi_21_32_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_32_bounds
  simp only [cot_pi_22_32_lower, cot_pi_22_32_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_32_bounds
  simp only [cot_pi_23_32_lower, cot_pi_23_32_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_32_bounds
  simp only [cot_pi_24_32_lower, cot_pi_24_32_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_32_bounds
  simp only [cot_pi_25_32_lower, cot_pi_25_32_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_32_bounds
  simp only [cot_pi_26_32_lower, cot_pi_26_32_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_32_bounds
  simp only [cot_pi_27_32_lower, cot_pi_27_32_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_32_bounds
  simp only [cot_pi_28_32_lower, cot_pi_28_32_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_32_bounds
  simp only [cot_pi_29_32_lower, cot_pi_29_32_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_32_bounds
  simp only [cot_pi_30_32_lower, cot_pi_30_32_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_32_bounds
  simp only [cot_pi_31_32_lower, cot_pi_31_32_upper] at b_cot_31
  rw [cotangentSumVFormula_49_32_lower, cotangentSumVFormula_49_32_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3249_formula_bound :
  (((121659410518904645129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 32 49) ∧
  (vasyuninBEntryFormula 32 49 ≤ ((121668417718163854871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 32 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log32 := prim_log_32_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_32_49_bounds
  have b_Vkh := cotangentSumVFormula_49_32_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_32_lower, prim_log_32_upper] at b_log32
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_32_49_lower, cotangentSumVFormula_32_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_32_lower, cotangentSumVFormula_49_32_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_33_49_unfold :
    cotangentSumVFormula 33 49 =
      ((33/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 33 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_33_49_lower : ℚ := -2170830632098453932979 / 439804651110400000000
def cotangentSumVFormula_33_49_upper : ℚ := -2170830623302042942021 / 439804651110400000000
theorem cotangentSumVFormula_33_49_bounds :
  ((cotangentSumVFormula_33_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 49 ∧
  cotangentSumVFormula 33 49 ≤ ((cotangentSumVFormula_33_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_49_unfold]
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
  rw [cotangentSumVFormula_33_49_lower, cotangentSumVFormula_33_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_33_unfold :
    cotangentSumVFormula 49 33 =
      ((16/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((14/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((13/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((10/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((7/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((5/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((2/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((17/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_49_33_lower : ℚ := 1817904396896929478823 / 219902325555200000000
def cotangentSumVFormula_49_33_upper : ℚ := 1817904401295051771177 / 219902325555200000000
theorem cotangentSumVFormula_49_33_bounds :
  ((cotangentSumVFormula_49_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 33 ∧
  cotangentSumVFormula 49 33 ≤ ((cotangentSumVFormula_49_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_33_unfold]
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
  rw [cotangentSumVFormula_49_33_lower, cotangentSumVFormula_49_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3349_formula_bound :
  (((60285730124719486627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 49) ∧
  (vasyuninBEntryFormula 33 49 ≤ ((30145116862174670749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_33_49_bounds
  have b_Vkh := cotangentSumVFormula_49_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_33_49_lower, cotangentSumVFormula_33_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_33_lower, cotangentSumVFormula_49_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_34_49_unfold :
    cotangentSumVFormula 34 49 =
      ((34/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 34 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_34_49_lower : ℚ := 1294332856357380024667 / 879609302220800000000
def cotangentSumVFormula_34_49_upper : ℚ := 1294332873950191850333 / 879609302220800000000
theorem cotangentSumVFormula_34_49_bounds :
  ((cotangentSumVFormula_34_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 34 49 ∧
  cotangentSumVFormula 34 49 ≤ ((cotangentSumVFormula_34_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_34_49_unfold]
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
  rw [cotangentSumVFormula_34_49_lower, cotangentSumVFormula_34_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_34_unfold :
    cotangentSumVFormula 49 34 =
      ((15/34 : ℚ) : ℝ) * cotangentTermV 1 34    + 
      ((30/34 : ℚ) : ℝ) * cotangentTermV 2 34    + 
      ((11/34 : ℚ) : ℝ) * cotangentTermV 3 34    + 
      ((26/34 : ℚ) : ℝ) * cotangentTermV 4 34    + 
      ((7/34 : ℚ) : ℝ) * cotangentTermV 5 34    + 
      ((22/34 : ℚ) : ℝ) * cotangentTermV 6 34    + 
      ((3/34 : ℚ) : ℝ) * cotangentTermV 7 34    + 
      ((18/34 : ℚ) : ℝ) * cotangentTermV 8 34    + 
      ((33/34 : ℚ) : ℝ) * cotangentTermV 9 34    + 
      ((14/34 : ℚ) : ℝ) * cotangentTermV 10 34    + 
      ((29/34 : ℚ) : ℝ) * cotangentTermV 11 34    + 
      ((10/34 : ℚ) : ℝ) * cotangentTermV 12 34    + 
      ((25/34 : ℚ) : ℝ) * cotangentTermV 13 34    + 
      ((6/34 : ℚ) : ℝ) * cotangentTermV 14 34    + 
      ((21/34 : ℚ) : ℝ) * cotangentTermV 15 34    + 
      ((2/34 : ℚ) : ℝ) * cotangentTermV 16 34    + 
      ((17/34 : ℚ) : ℝ) * cotangentTermV 17 34    + 
      ((32/34 : ℚ) : ℝ) * cotangentTermV 18 34    + 
      ((13/34 : ℚ) : ℝ) * cotangentTermV 19 34    + 
      ((28/34 : ℚ) : ℝ) * cotangentTermV 20 34    + 
      ((9/34 : ℚ) : ℝ) * cotangentTermV 21 34    + 
      ((24/34 : ℚ) : ℝ) * cotangentTermV 22 34    + 
      ((5/34 : ℚ) : ℝ) * cotangentTermV 23 34    + 
      ((20/34 : ℚ) : ℝ) * cotangentTermV 24 34    + 
      ((1/34 : ℚ) : ℝ) * cotangentTermV 25 34    + 
      ((16/34 : ℚ) : ℝ) * cotangentTermV 26 34    + 
      ((31/34 : ℚ) : ℝ) * cotangentTermV 27 34    + 
      ((12/34 : ℚ) : ℝ) * cotangentTermV 28 34    + 
      ((27/34 : ℚ) : ℝ) * cotangentTermV 29 34    + 
      ((8/34 : ℚ) : ℝ) * cotangentTermV 30 34    + 
      ((23/34 : ℚ) : ℝ) * cotangentTermV 31 34    + 
      ((4/34 : ℚ) : ℝ) * cotangentTermV 32 34    + 
      ((19/34 : ℚ) : ℝ) * cotangentTermV 33 34 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_34]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((15/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((30/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((11/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((26/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((7/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((22/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((3/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((18/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((33/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((14/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((29/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((10/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((25/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((6/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((21/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((2/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((17/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((32/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((13/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((28/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((9/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((24/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((5/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((20/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((1/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((16/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((31/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((12/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((27/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((8/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((23/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((4/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((19/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33]
  try ring

def cotangentSumVFormula_49_34_lower : ℚ := 1875480221327831587167 / 879609302220800000000
def cotangentSumVFormula_49_34_upper : ℚ := 1875480238920365287833 / 879609302220800000000
theorem cotangentSumVFormula_49_34_bounds :
  ((cotangentSumVFormula_49_34_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 34 ∧
  cotangentSumVFormula 49 34 ≤ ((cotangentSumVFormula_49_34_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_34_unfold]
  have b_cot_1 := cot_pi_1_34_bounds
  simp only [cot_pi_1_34_lower, cot_pi_1_34_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_34_bounds
  simp only [cot_pi_2_34_lower, cot_pi_2_34_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_34_bounds
  simp only [cot_pi_3_34_lower, cot_pi_3_34_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_34_bounds
  simp only [cot_pi_4_34_lower, cot_pi_4_34_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_34_bounds
  simp only [cot_pi_5_34_lower, cot_pi_5_34_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_34_bounds
  simp only [cot_pi_6_34_lower, cot_pi_6_34_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_34_bounds
  simp only [cot_pi_7_34_lower, cot_pi_7_34_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_34_bounds
  simp only [cot_pi_8_34_lower, cot_pi_8_34_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_34_bounds
  simp only [cot_pi_9_34_lower, cot_pi_9_34_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_34_bounds
  simp only [cot_pi_10_34_lower, cot_pi_10_34_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_34_bounds
  simp only [cot_pi_11_34_lower, cot_pi_11_34_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_34_bounds
  simp only [cot_pi_12_34_lower, cot_pi_12_34_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_34_bounds
  simp only [cot_pi_13_34_lower, cot_pi_13_34_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_34_bounds
  simp only [cot_pi_14_34_lower, cot_pi_14_34_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_34_bounds
  simp only [cot_pi_15_34_lower, cot_pi_15_34_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_34_bounds
  simp only [cot_pi_16_34_lower, cot_pi_16_34_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_34_bounds
  simp only [cot_pi_17_34_lower, cot_pi_17_34_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_34_bounds
  simp only [cot_pi_18_34_lower, cot_pi_18_34_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_34_bounds
  simp only [cot_pi_19_34_lower, cot_pi_19_34_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_34_bounds
  simp only [cot_pi_20_34_lower, cot_pi_20_34_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_34_bounds
  simp only [cot_pi_21_34_lower, cot_pi_21_34_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_34_bounds
  simp only [cot_pi_22_34_lower, cot_pi_22_34_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_34_bounds
  simp only [cot_pi_23_34_lower, cot_pi_23_34_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_34_bounds
  simp only [cot_pi_24_34_lower, cot_pi_24_34_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_34_bounds
  simp only [cot_pi_25_34_lower, cot_pi_25_34_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_34_bounds
  simp only [cot_pi_26_34_lower, cot_pi_26_34_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_34_bounds
  simp only [cot_pi_27_34_lower, cot_pi_27_34_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_34_bounds
  simp only [cot_pi_28_34_lower, cot_pi_28_34_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_34_bounds
  simp only [cot_pi_29_34_lower, cot_pi_29_34_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_34_bounds
  simp only [cot_pi_30_34_lower, cot_pi_30_34_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_34_bounds
  simp only [cot_pi_31_34_lower, cot_pi_31_34_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_34_bounds
  simp only [cot_pi_32_34_lower, cot_pi_32_34_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_34_bounds
  simp only [cot_pi_33_34_lower, cot_pi_33_34_upper] at b_cot_33
  rw [cotangentSumVFormula_49_34_lower, cotangentSumVFormula_49_34_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3449_formula_bound :
  (((59355358277175767877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 34 49) ∧
  (vasyuninBEntryFormula 34 49 ≤ ((59359861876805669623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 34 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log34 := prim_log_34_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_34_49_bounds
  have b_Vkh := cotangentSumVFormula_49_34_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_34_lower, prim_log_34_upper] at b_log34
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_34_49_lower, cotangentSumVFormula_34_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_34_lower, cotangentSumVFormula_49_34_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
