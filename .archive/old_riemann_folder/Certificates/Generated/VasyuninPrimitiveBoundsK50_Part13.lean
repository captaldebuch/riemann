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

theorem cotangentSumVFormula_36_49_unfold :
    cotangentSumVFormula 36 49 =
      ((36/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 36 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_36_49_lower : ℚ := 740084363661087200349 / 109951162777600000000
def cotangentSumVFormula_36_49_upper : ℚ := 370042182930092142013 / 54975581388800000000
theorem cotangentSumVFormula_36_49_bounds :
  ((cotangentSumVFormula_36_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 49 ∧
  cotangentSumVFormula 36 49 ≤ ((cotangentSumVFormula_36_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_49_unfold]
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
  rw [cotangentSumVFormula_36_49_lower, cotangentSumVFormula_36_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_36_unfold :
    cotangentSumVFormula 49 36 =
      ((13/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_49_36_lower : ℚ := -1277376809773678151729 / 439804651110400000000
def cotangentSumVFormula_49_36_upper : ℚ := -1277376800977402317021 / 439804651110400000000
theorem cotangentSumVFormula_49_36_bounds :
  ((cotangentSumVFormula_49_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 36 ∧
  cotangentSumVFormula 49 36 ≤ ((cotangentSumVFormula_49_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_36_unfold]
  have b_cot_1 := cot_pi_1_36_bounds
  simp only [cot_pi_1_36_lower, cot_pi_1_36_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_36_bounds
  simp only [cot_pi_2_36_lower, cot_pi_2_36_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_36_bounds
  simp only [cot_pi_3_36_lower, cot_pi_3_36_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_36_bounds
  simp only [cot_pi_4_36_lower, cot_pi_4_36_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_36_bounds
  simp only [cot_pi_5_36_lower, cot_pi_5_36_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_36_bounds
  simp only [cot_pi_6_36_lower, cot_pi_6_36_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_36_bounds
  simp only [cot_pi_7_36_lower, cot_pi_7_36_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_36_bounds
  simp only [cot_pi_8_36_lower, cot_pi_8_36_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_36_bounds
  simp only [cot_pi_9_36_lower, cot_pi_9_36_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_36_bounds
  simp only [cot_pi_10_36_lower, cot_pi_10_36_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_36_bounds
  simp only [cot_pi_11_36_lower, cot_pi_11_36_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_36_bounds
  simp only [cot_pi_12_36_lower, cot_pi_12_36_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_36_bounds
  simp only [cot_pi_13_36_lower, cot_pi_13_36_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_36_bounds
  simp only [cot_pi_14_36_lower, cot_pi_14_36_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_36_bounds
  simp only [cot_pi_15_36_lower, cot_pi_15_36_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_36_bounds
  simp only [cot_pi_16_36_lower, cot_pi_16_36_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_36_bounds
  simp only [cot_pi_17_36_lower, cot_pi_17_36_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_36_bounds
  simp only [cot_pi_18_36_lower, cot_pi_18_36_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_36_bounds
  simp only [cot_pi_19_36_lower, cot_pi_19_36_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_36_bounds
  simp only [cot_pi_20_36_lower, cot_pi_20_36_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_36_bounds
  simp only [cot_pi_21_36_lower, cot_pi_21_36_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_36_bounds
  simp only [cot_pi_22_36_lower, cot_pi_22_36_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_36_bounds
  simp only [cot_pi_23_36_lower, cot_pi_23_36_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_36_bounds
  simp only [cot_pi_24_36_lower, cot_pi_24_36_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_36_bounds
  simp only [cot_pi_25_36_lower, cot_pi_25_36_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_36_bounds
  simp only [cot_pi_26_36_lower, cot_pi_26_36_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_36_bounds
  simp only [cot_pi_27_36_lower, cot_pi_27_36_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_36_bounds
  simp only [cot_pi_28_36_lower, cot_pi_28_36_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_36_bounds
  simp only [cot_pi_29_36_lower, cot_pi_29_36_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_36_bounds
  simp only [cot_pi_30_36_lower, cot_pi_30_36_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_36_bounds
  simp only [cot_pi_31_36_lower, cot_pi_31_36_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_36_bounds
  simp only [cot_pi_32_36_lower, cot_pi_32_36_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_36_bounds
  simp only [cot_pi_33_36_lower, cot_pi_33_36_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_36_bounds
  simp only [cot_pi_34_36_lower, cot_pi_34_36_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_36_bounds
  simp only [cot_pi_35_36_lower, cot_pi_35_36_upper] at b_cot_35
  rw [cotangentSumVFormula_49_36_lower, cotangentSumVFormula_49_36_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3649_formula_bound :
  (((29080362286704454251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 36 49) ∧
  (vasyuninBEntryFormula 36 49 ≤ ((14541307043259655687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 36 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log36 := prim_log_36_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_36_49_bounds
  have b_Vkh := cotangentSumVFormula_49_36_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_36_49_lower, cotangentSumVFormula_36_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_36_lower, cotangentSumVFormula_49_36_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_49_unfold :
    cotangentSumVFormula 37 49 =
      ((37/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 37 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_37_49_lower : ℚ := 2083277938264187783709 / 1759218604441600000000
def cotangentSumVFormula_37_49_upper : ℚ := 2083277973449784091291 / 1759218604441600000000
theorem cotangentSumVFormula_37_49_bounds :
  ((cotangentSumVFormula_37_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 49 ∧
  cotangentSumVFormula 37 49 ≤ ((cotangentSumVFormula_37_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_49_unfold]
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
  rw [cotangentSumVFormula_37_49_lower, cotangentSumVFormula_37_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_37_unfold :
    cotangentSumVFormula 49 37 =
      ((12/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_49_37_lower : ℚ := 2333917607301461274667 / 879609302220800000000
def cotangentSumVFormula_49_37_upper : ℚ := 2333917624894038725333 / 879609302220800000000
theorem cotangentSumVFormula_49_37_bounds :
  ((cotangentSumVFormula_49_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 37 ∧
  cotangentSumVFormula 49 37 ≤ ((cotangentSumVFormula_49_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_37_unfold]
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
  rw [cotangentSumVFormula_49_37_lower, cotangentSumVFormula_49_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3749_formula_bound :
  (((115491824687292082629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 49) ∧
  (vasyuninBEntryFormula 37 49 ≤ ((115500831886551542371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_37_49_bounds
  have b_Vkh := cotangentSumVFormula_49_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_37_49_lower, cotangentSumVFormula_37_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_37_lower, cotangentSumVFormula_49_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_38_49_unfold :
    cotangentSumVFormula 38 49 =
      ((38/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 38 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_38_49_lower : ℚ := 1768044267223629478823 / 219902325555200000000
def cotangentSumVFormula_38_49_upper : ℚ := 1768044271621825989927 / 219902325555200000000
theorem cotangentSumVFormula_38_49_bounds :
  ((cotangentSumVFormula_38_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 49 ∧
  cotangentSumVFormula 38 49 ≤ ((cotangentSumVFormula_38_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_49_unfold]
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
  rw [cotangentSumVFormula_38_49_lower, cotangentSumVFormula_38_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_38_unfold :
    cotangentSumVFormula 49 38 =
      ((11/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_49_38_lower : ℚ := -454528040619067487151 / 109951162777600000000
def cotangentSumVFormula_49_38_upper : ℚ := -909056076839979478823 / 219902325555200000000
theorem cotangentSumVFormula_49_38_bounds :
  ((cotangentSumVFormula_49_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 38 ∧
  cotangentSumVFormula 49 38 ≤ ((cotangentSumVFormula_49_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_38_unfold]
  have b_cot_1 := cot_pi_1_38_bounds
  simp only [cot_pi_1_38_lower, cot_pi_1_38_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_38_bounds
  simp only [cot_pi_2_38_lower, cot_pi_2_38_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_38_bounds
  simp only [cot_pi_3_38_lower, cot_pi_3_38_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_38_bounds
  simp only [cot_pi_4_38_lower, cot_pi_4_38_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_38_bounds
  simp only [cot_pi_5_38_lower, cot_pi_5_38_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_38_bounds
  simp only [cot_pi_6_38_lower, cot_pi_6_38_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_38_bounds
  simp only [cot_pi_7_38_lower, cot_pi_7_38_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_38_bounds
  simp only [cot_pi_8_38_lower, cot_pi_8_38_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_38_bounds
  simp only [cot_pi_9_38_lower, cot_pi_9_38_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_38_bounds
  simp only [cot_pi_10_38_lower, cot_pi_10_38_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_38_bounds
  simp only [cot_pi_11_38_lower, cot_pi_11_38_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_38_bounds
  simp only [cot_pi_12_38_lower, cot_pi_12_38_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_38_bounds
  simp only [cot_pi_13_38_lower, cot_pi_13_38_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_38_bounds
  simp only [cot_pi_14_38_lower, cot_pi_14_38_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_38_bounds
  simp only [cot_pi_15_38_lower, cot_pi_15_38_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_38_bounds
  simp only [cot_pi_16_38_lower, cot_pi_16_38_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_38_bounds
  simp only [cot_pi_17_38_lower, cot_pi_17_38_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_38_bounds
  simp only [cot_pi_18_38_lower, cot_pi_18_38_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_38_bounds
  simp only [cot_pi_19_38_lower, cot_pi_19_38_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_38_bounds
  simp only [cot_pi_20_38_lower, cot_pi_20_38_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_38_bounds
  simp only [cot_pi_21_38_lower, cot_pi_21_38_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_38_bounds
  simp only [cot_pi_22_38_lower, cot_pi_22_38_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_38_bounds
  simp only [cot_pi_23_38_lower, cot_pi_23_38_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_38_bounds
  simp only [cot_pi_24_38_lower, cot_pi_24_38_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_38_bounds
  simp only [cot_pi_25_38_lower, cot_pi_25_38_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_38_bounds
  simp only [cot_pi_26_38_lower, cot_pi_26_38_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_38_bounds
  simp only [cot_pi_27_38_lower, cot_pi_27_38_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_38_bounds
  simp only [cot_pi_28_38_lower, cot_pi_28_38_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_38_bounds
  simp only [cot_pi_29_38_lower, cot_pi_29_38_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_38_bounds
  simp only [cot_pi_30_38_lower, cot_pi_30_38_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_38_bounds
  simp only [cot_pi_31_38_lower, cot_pi_31_38_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_38_bounds
  simp only [cot_pi_32_38_lower, cot_pi_32_38_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_38_bounds
  simp only [cot_pi_33_38_lower, cot_pi_33_38_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_38_bounds
  simp only [cot_pi_34_38_lower, cot_pi_34_38_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_38_bounds
  simp only [cot_pi_35_38_lower, cot_pi_35_38_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_38_bounds
  simp only [cot_pi_36_38_lower, cot_pi_36_38_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_38_bounds
  simp only [cot_pi_37_38_lower, cot_pi_37_38_upper] at b_cot_37
  rw [cotangentSumVFormula_49_38_lower, cotangentSumVFormula_49_38_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3849_formula_bound :
  (((114410624501690957629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 38 49) ∧
  (vasyuninBEntryFormula 38 49 ≤ ((114419631700950479871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 38 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log38 := prim_log_38_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_38_49_bounds
  have b_Vkh := cotangentSumVFormula_49_38_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_38_49_lower, cotangentSumVFormula_38_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_38_lower, cotangentSumVFormula_49_38_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_39_49_unfold :
    cotangentSumVFormula 39 49 =
      ((39/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 39 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_39_49_lower : ℚ := 2636567982898574010073 / 219902325555200000000
def cotangentSumVFormula_39_49_upper : ℚ := 2636567987296766614927 / 219902325555200000000
theorem cotangentSumVFormula_39_49_bounds :
  ((cotangentSumVFormula_39_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 49 ∧
  cotangentSumVFormula 39 49 ≤ ((cotangentSumVFormula_39_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_49_unfold]
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
  rw [cotangentSumVFormula_39_49_lower, cotangentSumVFormula_39_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_39_unfold :
    cotangentSumVFormula 49 39 =
      ((10/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_49_39_lower : ℚ := -446323646027439017013 / 54975581388800000000
def cotangentSumVFormula_49_39_upper : ℚ := -111580911231974718403 / 13743895347200000000
theorem cotangentSumVFormula_49_39_bounds :
  ((cotangentSumVFormula_49_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 39 ∧
  cotangentSumVFormula 49 39 ≤ ((cotangentSumVFormula_49_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_39_unfold]
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
  rw [cotangentSumVFormula_49_39_lower, cotangentSumVFormula_49_39_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3949_formula_bound :
  (((113697908736263270129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 39 49) ∧
  (vasyuninBEntryFormula 39 49 ≤ ((113706915935522698621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 39 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log39 := prim_log_39_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_39_49_bounds
  have b_Vkh := cotangentSumVFormula_49_39_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_39_49_lower, cotangentSumVFormula_39_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_39_lower, cotangentSumVFormula_49_39_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_40_49_unfold :
    cotangentSumVFormula 40 49 =
      ((40/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 40 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_40_49_lower : ℚ := 2226319202438154478823 / 219902325555200000000
def cotangentSumVFormula_40_49_upper : ℚ := 2226319206836340052427 / 219902325555200000000
theorem cotangentSumVFormula_40_49_bounds :
  ((cotangentSumVFormula_40_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 49 ∧
  cotangentSumVFormula 40 49 ≤ ((cotangentSumVFormula_40_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_49_unfold]
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
  rw [cotangentSumVFormula_40_49_lower, cotangentSumVFormula_40_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_40_unfold :
    cotangentSumVFormula 49 40 =
      ((9/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_49_40_lower : ℚ := -691514057291828424651 / 109951162777600000000
def cotangentSumVFormula_49_40_upper : ℚ := -1383028110185484166323 / 219902325555200000000
theorem cotangentSumVFormula_49_40_bounds :
  ((cotangentSumVFormula_49_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 40 ∧
  cotangentSumVFormula 49 40 ≤ ((cotangentSumVFormula_49_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_40_unfold]
  have b_cot_1 := cot_pi_1_40_bounds
  simp only [cot_pi_1_40_lower, cot_pi_1_40_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_40_bounds
  simp only [cot_pi_2_40_lower, cot_pi_2_40_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_40_bounds
  simp only [cot_pi_3_40_lower, cot_pi_3_40_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_40_bounds
  simp only [cot_pi_4_40_lower, cot_pi_4_40_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_40_bounds
  simp only [cot_pi_5_40_lower, cot_pi_5_40_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_40_bounds
  simp only [cot_pi_6_40_lower, cot_pi_6_40_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_40_bounds
  simp only [cot_pi_7_40_lower, cot_pi_7_40_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_40_bounds
  simp only [cot_pi_8_40_lower, cot_pi_8_40_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_40_bounds
  simp only [cot_pi_9_40_lower, cot_pi_9_40_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_40_bounds
  simp only [cot_pi_10_40_lower, cot_pi_10_40_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_40_bounds
  simp only [cot_pi_11_40_lower, cot_pi_11_40_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_40_bounds
  simp only [cot_pi_12_40_lower, cot_pi_12_40_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_40_bounds
  simp only [cot_pi_13_40_lower, cot_pi_13_40_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_40_bounds
  simp only [cot_pi_14_40_lower, cot_pi_14_40_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_40_bounds
  simp only [cot_pi_15_40_lower, cot_pi_15_40_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_40_bounds
  simp only [cot_pi_16_40_lower, cot_pi_16_40_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_40_bounds
  simp only [cot_pi_17_40_lower, cot_pi_17_40_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_40_bounds
  simp only [cot_pi_18_40_lower, cot_pi_18_40_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_40_bounds
  simp only [cot_pi_19_40_lower, cot_pi_19_40_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_40_bounds
  simp only [cot_pi_20_40_lower, cot_pi_20_40_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_40_bounds
  simp only [cot_pi_21_40_lower, cot_pi_21_40_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_40_bounds
  simp only [cot_pi_22_40_lower, cot_pi_22_40_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_40_bounds
  simp only [cot_pi_23_40_lower, cot_pi_23_40_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_40_bounds
  simp only [cot_pi_24_40_lower, cot_pi_24_40_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_40_bounds
  simp only [cot_pi_25_40_lower, cot_pi_25_40_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_40_bounds
  simp only [cot_pi_26_40_lower, cot_pi_26_40_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_40_bounds
  simp only [cot_pi_27_40_lower, cot_pi_27_40_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_40_bounds
  simp only [cot_pi_28_40_lower, cot_pi_28_40_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_40_bounds
  simp only [cot_pi_29_40_lower, cot_pi_29_40_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_40_bounds
  simp only [cot_pi_30_40_lower, cot_pi_30_40_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_40_bounds
  simp only [cot_pi_31_40_lower, cot_pi_31_40_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_40_bounds
  simp only [cot_pi_32_40_lower, cot_pi_32_40_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_40_bounds
  simp only [cot_pi_33_40_lower, cot_pi_33_40_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_40_bounds
  simp only [cot_pi_34_40_lower, cot_pi_34_40_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_40_bounds
  simp only [cot_pi_35_40_lower, cot_pi_35_40_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_40_bounds
  simp only [cot_pi_36_40_lower, cot_pi_36_40_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_40_bounds
  simp only [cot_pi_37_40_lower, cot_pi_37_40_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_40_bounds
  simp only [cot_pi_38_40_lower, cot_pi_38_40_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_40_bounds
  simp only [cot_pi_39_40_lower, cot_pi_39_40_upper] at b_cot_39
  rw [cotangentSumVFormula_49_40_lower, cotangentSumVFormula_49_40_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4049_formula_bound :
  (((56479367028042330377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 40 49) ∧
  (vasyuninBEntryFormula 40 49 ≤ ((14120967656917999437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 40 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log40 := prim_log_40_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_40_49_bounds
  have b_Vkh := cotangentSumVFormula_49_40_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_40_49_lower, cotangentSumVFormula_40_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_40_lower, cotangentSumVFormula_49_40_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_49_unfold :
    cotangentSumVFormula 41 49 =
      ((41/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 41 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_41_49_lower : ℚ := 1925455667977738072573 / 219902325555200000000
def cotangentSumVFormula_41_49_upper : ℚ := 1925455672375925208677 / 219902325555200000000
theorem cotangentSumVFormula_41_49_bounds :
  ((cotangentSumVFormula_41_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 49 ∧
  cotangentSumVFormula 41 49 ≤ ((cotangentSumVFormula_41_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_49_unfold]
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
  rw [cotangentSumVFormula_41_49_lower, cotangentSumVFormula_41_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_41_unfold :
    cotangentSumVFormula 49 41 =
      ((8/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((6/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((5/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((4/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((3/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((2/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((1/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((9/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_49_41_lower : ℚ := -34557585911233148611 / 6871947673600000000
def cotangentSumVFormula_49_41_upper : ℚ := -552921372380646575349 / 109951162777600000000
theorem cotangentSumVFormula_49_41_bounds :
  ((cotangentSumVFormula_49_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 41 ∧
  cotangentSumVFormula 49 41 ≤ ((cotangentSumVFormula_49_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_41_unfold]
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
  rw [cotangentSumVFormula_49_41_lower, cotangentSumVFormula_49_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4149_formula_bound :
  (((112444591557254863879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 49) ∧
  (vasyuninBEntryFormula 41 49 ≤ ((112453598756514042371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_41_49_bounds
  have b_Vkh := cotangentSumVFormula_49_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_41_49_lower, cotangentSumVFormula_41_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_41_lower, cotangentSumVFormula_49_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_43_49_unfold :
    cotangentSumVFormula 43 49 =
      ((43/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 43 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_43_49_lower : ℚ := 750823052774344576737 / 54975581388800000000
def cotangentSumVFormula_43_49_upper : ℚ := 750823053873895267013 / 54975581388800000000
theorem cotangentSumVFormula_43_49_bounds :
  ((cotangentSumVFormula_43_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 49 ∧
  cotangentSumVFormula 43 49 ≤ ((cotangentSumVFormula_43_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_49_unfold]
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
  rw [cotangentSumVFormula_43_49_lower, cotangentSumVFormula_43_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_43_unfold :
    cotangentSumVFormula 49 43 =
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
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 49 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_49_43_lower : ℚ := -2257714267322599427427 / 219902325555200000000
def cotangentSumVFormula_49_43_upper : ℚ := -2257714262924374791323 / 219902325555200000000
theorem cotangentSumVFormula_49_43_bounds :
  ((cotangentSumVFormula_49_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 43 ∧
  cotangentSumVFormula 49 43 ≤ ((cotangentSumVFormula_49_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_43_unfold]
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
  rw [cotangentSumVFormula_49_43_lower, cotangentSumVFormula_49_43_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4349_formula_bound :
  (((55862887365105611627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 43 49) ∧
  (vasyuninBEntryFormula 43 49 ≤ ((436463991911997541 / 17592186044416000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 43 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log43 := log_43_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_43_49_bounds
  have b_Vkh := cotangentSumVFormula_49_43_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_43_49_lower, cotangentSumVFormula_43_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_43_lower, cotangentSumVFormula_49_43_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_44_49_unfold :
    cotangentSumVFormula 44 49 =
      ((44/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 44 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_44_49_lower : ℚ := 2024816866223509856599 / 109951162777600000000
def cotangentSumVFormula_44_49_upper : ℚ := 2024816868422619830901 / 109951162777600000000
theorem cotangentSumVFormula_44_49_bounds :
  ((cotangentSumVFormula_44_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 49 ∧
  cotangentSumVFormula 44 49 ≤ ((cotangentSumVFormula_44_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_49_unfold]
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
  rw [cotangentSumVFormula_44_49_lower, cotangentSumVFormula_44_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_44_unfold :
    cotangentSumVFormula 49 44 =
      ((5/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 49 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_49_44_lower : ℚ := -3360474024607540052427 / 219902325555200000000
def cotangentSumVFormula_49_44_upper : ℚ := -3360474020209309166323 / 219902325555200000000
theorem cotangentSumVFormula_49_44_bounds :
  ((cotangentSumVFormula_49_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 44 ∧
  cotangentSumVFormula 49 44 ≤ ((cotangentSumVFormula_49_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_44_unfold]
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
  rw [cotangentSumVFormula_49_44_lower, cotangentSumVFormula_49_44_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4449_formula_bound :
  (((13950178731393344313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 44 49) ∧
  (vasyuninBEntryFormula 44 49 ≤ ((55805218525203544623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 44 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log44 := prim_log_44_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_44_49_bounds
  have b_Vkh := cotangentSumVFormula_49_44_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_44_49_lower, cotangentSumVFormula_44_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_44_lower, cotangentSumVFormula_49_44_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_45_49_unfold :
    cotangentSumVFormula 45 49 =
      ((45/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 45 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_45_49_lower : ℚ := 2219509023902338762849 / 109951162777600000000
def cotangentSumVFormula_45_49_upper : ℚ := 2219509026101447955901 / 109951162777600000000
theorem cotangentSumVFormula_45_49_bounds :
  ((cotangentSumVFormula_45_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 49 ∧
  cotangentSumVFormula 45 49 ≤ ((cotangentSumVFormula_45_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_49_unfold]
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
  rw [cotangentSumVFormula_45_49_lower, cotangentSumVFormula_45_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_45_unfold :
    cotangentSumVFormula 49 45 =
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
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 49 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_49_45_lower : ℚ := -1911087737409046393401 / 109951162777600000000
def cotangentSumVFormula_49_45_upper : ℚ := -1911087735209925481599 / 109951162777600000000
theorem cotangentSumVFormula_49_45_bounds :
  ((cotangentSumVFormula_49_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 45 ∧
  cotangentSumVFormula 49 45 ≤ ((cotangentSumVFormula_49_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_45_unfold]
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
  rw [cotangentSumVFormula_49_45_lower, cotangentSumVFormula_49_45_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4549_formula_bound :
  (((27916375852914798001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 45 49) ∧
  (vasyuninBEntryFormula 45 49 ≤ ((55837255305459794623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 45 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log45 := prim_log_45_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_45_49_bounds
  have b_Vkh := cotangentSumVFormula_49_45_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_45_49_lower, cotangentSumVFormula_45_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_45_lower, cotangentSumVFormula_49_45_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_46_49_unfold :
    cotangentSumVFormula 46 49 =
      ((46/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 46 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_46_49_lower : ℚ := 84741433890182058507 / 3435973836800000000
def cotangentSumVFormula_46_49_upper : ℚ := 1355862943342467923263 / 54975581388800000000
theorem cotangentSumVFormula_46_49_bounds :
  ((cotangentSumVFormula_46_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 49 ∧
  cotangentSumVFormula 46 49 ≤ ((cotangentSumVFormula_46_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_49_unfold]
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
  rw [cotangentSumVFormula_46_49_lower, cotangentSumVFormula_46_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_46_unfold :
    cotangentSumVFormula 49 46 =
      ((3/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 49 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_49_46_lower : ℚ := -2449081312152877643401 / 109951162777600000000
def cotangentSumVFormula_49_46_upper : ℚ := -2449081309953749700349 / 109951162777600000000
theorem cotangentSumVFormula_49_46_bounds :
  ((cotangentSumVFormula_49_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 46 ∧
  cotangentSumVFormula 49 46 ≤ ((cotangentSumVFormula_49_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_46_unfold]
  have b_cot_1 := cot_pi_1_46_bounds
  simp only [cot_pi_1_46_lower, cot_pi_1_46_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_46_bounds
  simp only [cot_pi_2_46_lower, cot_pi_2_46_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_46_bounds
  simp only [cot_pi_3_46_lower, cot_pi_3_46_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_46_bounds
  simp only [cot_pi_4_46_lower, cot_pi_4_46_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_46_bounds
  simp only [cot_pi_5_46_lower, cot_pi_5_46_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_46_bounds
  simp only [cot_pi_6_46_lower, cot_pi_6_46_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_46_bounds
  simp only [cot_pi_7_46_lower, cot_pi_7_46_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_46_bounds
  simp only [cot_pi_8_46_lower, cot_pi_8_46_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_46_bounds
  simp only [cot_pi_9_46_lower, cot_pi_9_46_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_46_bounds
  simp only [cot_pi_10_46_lower, cot_pi_10_46_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_46_bounds
  simp only [cot_pi_11_46_lower, cot_pi_11_46_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_46_bounds
  simp only [cot_pi_12_46_lower, cot_pi_12_46_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_46_bounds
  simp only [cot_pi_13_46_lower, cot_pi_13_46_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_46_bounds
  simp only [cot_pi_14_46_lower, cot_pi_14_46_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_46_bounds
  simp only [cot_pi_15_46_lower, cot_pi_15_46_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_46_bounds
  simp only [cot_pi_16_46_lower, cot_pi_16_46_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_46_bounds
  simp only [cot_pi_17_46_lower, cot_pi_17_46_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_46_bounds
  simp only [cot_pi_18_46_lower, cot_pi_18_46_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_46_bounds
  simp only [cot_pi_19_46_lower, cot_pi_19_46_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_46_bounds
  simp only [cot_pi_20_46_lower, cot_pi_20_46_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_46_bounds
  simp only [cot_pi_21_46_lower, cot_pi_21_46_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_46_bounds
  simp only [cot_pi_22_46_lower, cot_pi_22_46_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_46_bounds
  simp only [cot_pi_23_46_lower, cot_pi_23_46_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_46_bounds
  simp only [cot_pi_24_46_lower, cot_pi_24_46_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_46_bounds
  simp only [cot_pi_25_46_lower, cot_pi_25_46_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_46_bounds
  simp only [cot_pi_26_46_lower, cot_pi_26_46_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_46_bounds
  simp only [cot_pi_27_46_lower, cot_pi_27_46_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_46_bounds
  simp only [cot_pi_28_46_lower, cot_pi_28_46_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_46_bounds
  simp only [cot_pi_29_46_lower, cot_pi_29_46_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_46_bounds
  simp only [cot_pi_30_46_lower, cot_pi_30_46_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_46_bounds
  simp only [cot_pi_31_46_lower, cot_pi_31_46_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_46_bounds
  simp only [cot_pi_32_46_lower, cot_pi_32_46_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_46_bounds
  simp only [cot_pi_33_46_lower, cot_pi_33_46_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_46_bounds
  simp only [cot_pi_34_46_lower, cot_pi_34_46_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_46_bounds
  simp only [cot_pi_35_46_lower, cot_pi_35_46_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_46_bounds
  simp only [cot_pi_36_46_lower, cot_pi_36_46_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_46_bounds
  simp only [cot_pi_37_46_lower, cot_pi_37_46_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_46_bounds
  simp only [cot_pi_38_46_lower, cot_pi_38_46_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_46_bounds
  simp only [cot_pi_39_46_lower, cot_pi_39_46_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_46_bounds
  simp only [cot_pi_40_46_lower, cot_pi_40_46_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_46_bounds
  simp only [cot_pi_41_46_lower, cot_pi_41_46_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_46_bounds
  simp only [cot_pi_42_46_lower, cot_pi_42_46_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_46_bounds
  simp only [cot_pi_43_46_lower, cot_pi_43_46_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_46_bounds
  simp only [cot_pi_44_46_lower, cot_pi_44_46_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_46_bounds
  simp only [cot_pi_45_46_lower, cot_pi_45_46_upper] at b_cot_45
  rw [cotangentSumVFormula_49_46_lower, cotangentSumVFormula_49_46_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4649_formula_bound :
  (((55977478155144017877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 46 49) ∧
  (vasyuninBEntryFormula 46 49 ≤ ((55981981754774263373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 46 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log46 := prim_log_46_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_46_49_bounds
  have b_Vkh := cotangentSumVFormula_49_46_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_46_49_lower, cotangentSumVFormula_46_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_46_lower, cotangentSumVFormula_49_46_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_47_49_unfold :
    cotangentSumVFormula 47 49 =
      ((47/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((48/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 47 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_47_49_lower : ℚ := 3393450887441323137849 / 109951162777600000000
def cotangentSumVFormula_47_49_upper : ℚ := 3393450889640435455901 / 109951162777600000000
theorem cotangentSumVFormula_47_49_bounds :
  ((cotangentSumVFormula_47_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 49 ∧
  cotangentSumVFormula 47 49 ≤ ((cotangentSumVFormula_47_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_49_unfold]
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
  rw [cotangentSumVFormula_47_49_lower, cotangentSumVFormula_47_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_47_unfold :
    cotangentSumVFormula 49 47 =
      ((2/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 49 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_49_47_lower : ℚ := -3189242832529579205901 / 109951162777600000000
def cotangentSumVFormula_49_47_upper : ℚ := -3189242830330444231599 / 109951162777600000000
theorem cotangentSumVFormula_49_47_bounds :
  ((cotangentSumVFormula_49_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 47 ∧
  cotangentSumVFormula 49 47 ≤ ((cotangentSumVFormula_49_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_47_unfold]
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
  rw [cotangentSumVFormula_49_47_lower, cotangentSumVFormula_49_47_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4749_formula_bound :
  (((14067733630136656813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 47 49) ∧
  (vasyuninBEntryFormula 47 49 ≤ ((56275438120176919623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 47 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log47 := log_47_certified_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_47_49_bounds
  have b_Vkh := cotangentSumVFormula_49_47_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_47_49_lower, cotangentSumVFormula_47_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_47_lower, cotangentSumVFormula_49_47_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_48_49_unfold :
    cotangentSumVFormula 48 49 =
      ((48/49 : ℚ) : ℝ) * cotangentTermV 1 49    + 
      ((47/49 : ℚ) : ℝ) * cotangentTermV 2 49    + 
      ((46/49 : ℚ) : ℝ) * cotangentTermV 3 49    + 
      ((45/49 : ℚ) : ℝ) * cotangentTermV 4 49    + 
      ((44/49 : ℚ) : ℝ) * cotangentTermV 5 49    + 
      ((43/49 : ℚ) : ℝ) * cotangentTermV 6 49    + 
      ((42/49 : ℚ) : ℝ) * cotangentTermV 7 49    + 
      ((41/49 : ℚ) : ℝ) * cotangentTermV 8 49    + 
      ((40/49 : ℚ) : ℝ) * cotangentTermV 9 49    + 
      ((39/49 : ℚ) : ℝ) * cotangentTermV 10 49    + 
      ((38/49 : ℚ) : ℝ) * cotangentTermV 11 49    + 
      ((37/49 : ℚ) : ℝ) * cotangentTermV 12 49    + 
      ((36/49 : ℚ) : ℝ) * cotangentTermV 13 49    + 
      ((35/49 : ℚ) : ℝ) * cotangentTermV 14 49    + 
      ((34/49 : ℚ) : ℝ) * cotangentTermV 15 49    + 
      ((33/49 : ℚ) : ℝ) * cotangentTermV 16 49    + 
      ((32/49 : ℚ) : ℝ) * cotangentTermV 17 49    + 
      ((31/49 : ℚ) : ℝ) * cotangentTermV 18 49    + 
      ((30/49 : ℚ) : ℝ) * cotangentTermV 19 49    + 
      ((29/49 : ℚ) : ℝ) * cotangentTermV 20 49    + 
      ((28/49 : ℚ) : ℝ) * cotangentTermV 21 49    + 
      ((27/49 : ℚ) : ℝ) * cotangentTermV 22 49    + 
      ((26/49 : ℚ) : ℝ) * cotangentTermV 23 49    + 
      ((25/49 : ℚ) : ℝ) * cotangentTermV 24 49    + 
      ((24/49 : ℚ) : ℝ) * cotangentTermV 25 49    + 
      ((23/49 : ℚ) : ℝ) * cotangentTermV 26 49    + 
      ((22/49 : ℚ) : ℝ) * cotangentTermV 27 49    + 
      ((21/49 : ℚ) : ℝ) * cotangentTermV 28 49    + 
      ((20/49 : ℚ) : ℝ) * cotangentTermV 29 49    + 
      ((19/49 : ℚ) : ℝ) * cotangentTermV 30 49    + 
      ((18/49 : ℚ) : ℝ) * cotangentTermV 31 49    + 
      ((17/49 : ℚ) : ℝ) * cotangentTermV 32 49    + 
      ((16/49 : ℚ) : ℝ) * cotangentTermV 33 49    + 
      ((15/49 : ℚ) : ℝ) * cotangentTermV 34 49    + 
      ((14/49 : ℚ) : ℝ) * cotangentTermV 35 49    + 
      ((13/49 : ℚ) : ℝ) * cotangentTermV 36 49    + 
      ((12/49 : ℚ) : ℝ) * cotangentTermV 37 49    + 
      ((11/49 : ℚ) : ℝ) * cotangentTermV 38 49    + 
      ((10/49 : ℚ) : ℝ) * cotangentTermV 39 49    + 
      ((9/49 : ℚ) : ℝ) * cotangentTermV 40 49    + 
      ((8/49 : ℚ) : ℝ) * cotangentTermV 41 49    + 
      ((7/49 : ℚ) : ℝ) * cotangentTermV 42 49    + 
      ((6/49 : ℚ) : ℝ) * cotangentTermV 43 49    + 
      ((5/49 : ℚ) : ℝ) * cotangentTermV 44 49    + 
      ((4/49 : ℚ) : ℝ) * cotangentTermV 45 49    + 
      ((3/49 : ℚ) : ℝ) * cotangentTermV 46 49    + 
      ((2/49 : ℚ) : ℝ) * cotangentTermV 47 49    + 
      ((1/49 : ℚ) : ℝ) * cotangentTermV 48 49 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_49]
  have hf_1 : Int.fract (((1 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((48/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((47/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((46/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((45/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((44/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((43/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((42/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((41/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((40/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((39/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((38/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((37/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((36/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((35/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((34/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((33/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((32/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((31/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((30/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((29/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((28/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((27/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((26/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((25/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((24/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((23/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((22/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((21/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((20/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((19/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((18/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((17/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((16/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((15/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((14/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((13/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((12/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((11/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((10/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((9/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((8/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((7/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((6/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((5/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((4/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((3/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((2/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 48 : ℕ) : ℝ) / ((49 : ℕ) : ℝ)) = ((1/49 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48]
  try ring

def cotangentSumVFormula_48_49_lower : ℚ := 1136860974877774046181 / 27487790694400000000
def cotangentSumVFormula_48_49_upper : ℚ := 1136860975427551735069 / 27487790694400000000
theorem cotangentSumVFormula_48_49_bounds :
  ((cotangentSumVFormula_48_49_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 48 49 ∧
  cotangentSumVFormula 48 49 ≤ ((cotangentSumVFormula_48_49_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_48_49_unfold]
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
  rw [cotangentSumVFormula_48_49_lower, cotangentSumVFormula_48_49_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_49_48_unfold :
    cotangentSumVFormula 49 48 =
      ((1/48 : ℚ) : ℝ) * cotangentTermV 1 48    + 
      ((2/48 : ℚ) : ℝ) * cotangentTermV 2 48    + 
      ((3/48 : ℚ) : ℝ) * cotangentTermV 3 48    + 
      ((4/48 : ℚ) : ℝ) * cotangentTermV 4 48    + 
      ((5/48 : ℚ) : ℝ) * cotangentTermV 5 48    + 
      ((6/48 : ℚ) : ℝ) * cotangentTermV 6 48    + 
      ((7/48 : ℚ) : ℝ) * cotangentTermV 7 48    + 
      ((8/48 : ℚ) : ℝ) * cotangentTermV 8 48    + 
      ((9/48 : ℚ) : ℝ) * cotangentTermV 9 48    + 
      ((10/48 : ℚ) : ℝ) * cotangentTermV 10 48    + 
      ((11/48 : ℚ) : ℝ) * cotangentTermV 11 48    + 
      ((12/48 : ℚ) : ℝ) * cotangentTermV 12 48    + 
      ((13/48 : ℚ) : ℝ) * cotangentTermV 13 48    + 
      ((14/48 : ℚ) : ℝ) * cotangentTermV 14 48    + 
      ((15/48 : ℚ) : ℝ) * cotangentTermV 15 48    + 
      ((16/48 : ℚ) : ℝ) * cotangentTermV 16 48    + 
      ((17/48 : ℚ) : ℝ) * cotangentTermV 17 48    + 
      ((18/48 : ℚ) : ℝ) * cotangentTermV 18 48    + 
      ((19/48 : ℚ) : ℝ) * cotangentTermV 19 48    + 
      ((20/48 : ℚ) : ℝ) * cotangentTermV 20 48    + 
      ((21/48 : ℚ) : ℝ) * cotangentTermV 21 48    + 
      ((22/48 : ℚ) : ℝ) * cotangentTermV 22 48    + 
      ((23/48 : ℚ) : ℝ) * cotangentTermV 23 48    + 
      ((24/48 : ℚ) : ℝ) * cotangentTermV 24 48    + 
      ((25/48 : ℚ) : ℝ) * cotangentTermV 25 48    + 
      ((26/48 : ℚ) : ℝ) * cotangentTermV 26 48    + 
      ((27/48 : ℚ) : ℝ) * cotangentTermV 27 48    + 
      ((28/48 : ℚ) : ℝ) * cotangentTermV 28 48    + 
      ((29/48 : ℚ) : ℝ) * cotangentTermV 29 48    + 
      ((30/48 : ℚ) : ℝ) * cotangentTermV 30 48    + 
      ((31/48 : ℚ) : ℝ) * cotangentTermV 31 48    + 
      ((32/48 : ℚ) : ℝ) * cotangentTermV 32 48    + 
      ((33/48 : ℚ) : ℝ) * cotangentTermV 33 48    + 
      ((34/48 : ℚ) : ℝ) * cotangentTermV 34 48    + 
      ((35/48 : ℚ) : ℝ) * cotangentTermV 35 48    + 
      ((36/48 : ℚ) : ℝ) * cotangentTermV 36 48    + 
      ((37/48 : ℚ) : ℝ) * cotangentTermV 37 48    + 
      ((38/48 : ℚ) : ℝ) * cotangentTermV 38 48    + 
      ((39/48 : ℚ) : ℝ) * cotangentTermV 39 48    + 
      ((40/48 : ℚ) : ℝ) * cotangentTermV 40 48    + 
      ((41/48 : ℚ) : ℝ) * cotangentTermV 41 48    + 
      ((42/48 : ℚ) : ℝ) * cotangentTermV 42 48    + 
      ((43/48 : ℚ) : ℝ) * cotangentTermV 43 48    + 
      ((44/48 : ℚ) : ℝ) * cotangentTermV 44 48    + 
      ((45/48 : ℚ) : ℝ) * cotangentTermV 45 48    + 
      ((46/48 : ℚ) : ℝ) * cotangentTermV 46 48    + 
      ((47/48 : ℚ) : ℝ) * cotangentTermV 47 48 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_48]
  have hf_1 : Int.fract (((1 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((1/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((2/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((3/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((4/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((5/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((6/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((7/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((8/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((9/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((10/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((11/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((12/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((13/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((14/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((15/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((16/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((17/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((18/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((19/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((20/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((21/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((22/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((23/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((24/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((25/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((26/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((27/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((28/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((29/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((30/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((31/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((32/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((33/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((34/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((35/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((36/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((37/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((38/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((39/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((40/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((41/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((42/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((43/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((44/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((45/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((46/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 49 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((47/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47]
  try ring

def cotangentSumVFormula_49_48_lower : ℚ := -2210361147933589017013 / 54975581388800000000
def cotangentSumVFormula_49_48_upper : ℚ := -2210361146834032857987 / 54975581388800000000
theorem cotangentSumVFormula_49_48_bounds :
  ((cotangentSumVFormula_49_48_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 49 48 ∧
  cotangentSumVFormula 49 48 ≤ ((cotangentSumVFormula_49_48_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_49_48_unfold]
  have b_cot_1 := cot_pi_1_48_bounds
  simp only [cot_pi_1_48_lower, cot_pi_1_48_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_48_bounds
  simp only [cot_pi_2_48_lower, cot_pi_2_48_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_48_bounds
  simp only [cot_pi_3_48_lower, cot_pi_3_48_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_48_bounds
  simp only [cot_pi_4_48_lower, cot_pi_4_48_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_48_bounds
  simp only [cot_pi_5_48_lower, cot_pi_5_48_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_48_bounds
  simp only [cot_pi_6_48_lower, cot_pi_6_48_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_48_bounds
  simp only [cot_pi_7_48_lower, cot_pi_7_48_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_48_bounds
  simp only [cot_pi_8_48_lower, cot_pi_8_48_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_48_bounds
  simp only [cot_pi_9_48_lower, cot_pi_9_48_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_48_bounds
  simp only [cot_pi_10_48_lower, cot_pi_10_48_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_48_bounds
  simp only [cot_pi_11_48_lower, cot_pi_11_48_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_48_bounds
  simp only [cot_pi_12_48_lower, cot_pi_12_48_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_48_bounds
  simp only [cot_pi_13_48_lower, cot_pi_13_48_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_48_bounds
  simp only [cot_pi_14_48_lower, cot_pi_14_48_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_48_bounds
  simp only [cot_pi_15_48_lower, cot_pi_15_48_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_48_bounds
  simp only [cot_pi_16_48_lower, cot_pi_16_48_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_48_bounds
  simp only [cot_pi_17_48_lower, cot_pi_17_48_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_48_bounds
  simp only [cot_pi_18_48_lower, cot_pi_18_48_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_48_bounds
  simp only [cot_pi_19_48_lower, cot_pi_19_48_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_48_bounds
  simp only [cot_pi_20_48_lower, cot_pi_20_48_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_48_bounds
  simp only [cot_pi_21_48_lower, cot_pi_21_48_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_48_bounds
  simp only [cot_pi_22_48_lower, cot_pi_22_48_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_48_bounds
  simp only [cot_pi_23_48_lower, cot_pi_23_48_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_48_bounds
  simp only [cot_pi_24_48_lower, cot_pi_24_48_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_48_bounds
  simp only [cot_pi_25_48_lower, cot_pi_25_48_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_48_bounds
  simp only [cot_pi_26_48_lower, cot_pi_26_48_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_48_bounds
  simp only [cot_pi_27_48_lower, cot_pi_27_48_upper] at b_cot_27
  have b_cot_28 := cot_pi_28_48_bounds
  simp only [cot_pi_28_48_lower, cot_pi_28_48_upper] at b_cot_28
  have b_cot_29 := cot_pi_29_48_bounds
  simp only [cot_pi_29_48_lower, cot_pi_29_48_upper] at b_cot_29
  have b_cot_30 := cot_pi_30_48_bounds
  simp only [cot_pi_30_48_lower, cot_pi_30_48_upper] at b_cot_30
  have b_cot_31 := cot_pi_31_48_bounds
  simp only [cot_pi_31_48_lower, cot_pi_31_48_upper] at b_cot_31
  have b_cot_32 := cot_pi_32_48_bounds
  simp only [cot_pi_32_48_lower, cot_pi_32_48_upper] at b_cot_32
  have b_cot_33 := cot_pi_33_48_bounds
  simp only [cot_pi_33_48_lower, cot_pi_33_48_upper] at b_cot_33
  have b_cot_34 := cot_pi_34_48_bounds
  simp only [cot_pi_34_48_lower, cot_pi_34_48_upper] at b_cot_34
  have b_cot_35 := cot_pi_35_48_bounds
  simp only [cot_pi_35_48_lower, cot_pi_35_48_upper] at b_cot_35
  have b_cot_36 := cot_pi_36_48_bounds
  simp only [cot_pi_36_48_lower, cot_pi_36_48_upper] at b_cot_36
  have b_cot_37 := cot_pi_37_48_bounds
  simp only [cot_pi_37_48_lower, cot_pi_37_48_upper] at b_cot_37
  have b_cot_38 := cot_pi_38_48_bounds
  simp only [cot_pi_38_48_lower, cot_pi_38_48_upper] at b_cot_38
  have b_cot_39 := cot_pi_39_48_bounds
  simp only [cot_pi_39_48_lower, cot_pi_39_48_upper] at b_cot_39
  have b_cot_40 := cot_pi_40_48_bounds
  simp only [cot_pi_40_48_lower, cot_pi_40_48_upper] at b_cot_40
  have b_cot_41 := cot_pi_41_48_bounds
  simp only [cot_pi_41_48_lower, cot_pi_41_48_upper] at b_cot_41
  have b_cot_42 := cot_pi_42_48_bounds
  simp only [cot_pi_42_48_lower, cot_pi_42_48_upper] at b_cot_42
  have b_cot_43 := cot_pi_43_48_bounds
  simp only [cot_pi_43_48_lower, cot_pi_43_48_upper] at b_cot_43
  have b_cot_44 := cot_pi_44_48_bounds
  simp only [cot_pi_44_48_lower, cot_pi_44_48_upper] at b_cot_44
  have b_cot_45 := cot_pi_45_48_bounds
  simp only [cot_pi_45_48_lower, cot_pi_45_48_upper] at b_cot_45
  have b_cot_46 := cot_pi_46_48_bounds
  simp only [cot_pi_46_48_lower, cot_pi_46_48_upper] at b_cot_46
  have b_cot_47 := cot_pi_47_48_bounds
  simp only [cot_pi_47_48_lower, cot_pi_47_48_upper] at b_cot_47
  rw [cotangentSumVFormula_49_48_lower, cotangentSumVFormula_49_48_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4849_formula_bound :
  (((28395957866072954251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 48 49) ∧
  (vasyuninBEntryFormula 48 49 ≤ ((56796419331775825873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 48 49 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log48 := prim_log_48_bounds
  have b_log49 := prim_log_49_bounds
  have b_Vhk := cotangentSumVFormula_48_49_bounds
  have b_Vkh := cotangentSumVFormula_49_48_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_48_lower, prim_log_48_upper] at b_log48
  simp only [prim_log_49_lower, prim_log_49_upper] at b_log49
  simp only [cotangentSumVFormula_48_49_lower, cotangentSumVFormula_48_49_upper] at b_Vhk
  simp only [cotangentSumVFormula_49_48_lower, cotangentSumVFormula_49_48_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_50_unfold :
    cotangentSumVFormula 1 50 =
      ((1/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 1 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_1_50_lower : ℚ := -584359997032204969097 / 13743895347200000000
def cotangentSumVFormula_1_50_upper : ℚ := -1168719993514625608681 / 27487790694400000000
theorem cotangentSumVFormula_1_50_bounds :
  ((cotangentSumVFormula_1_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 50 ∧
  cotangentSumVFormula 1 50 ≤ ((cotangentSumVFormula_1_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_50_unfold]
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
  rw [cotangentSumVFormula_1_50_lower, cotangentSumVFormula_1_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_1_unfold :
    cotangentSumVFormula 50 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_50_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_50_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_50_1_bounds :
  ((cotangentSumVFormula_50_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 1 ∧
  cotangentSumVFormula 50 1 ≤ ((cotangentSumVFormula_50_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_1_unfold]
  rw [cotangentSumVFormula_50_1_lower, cotangentSumVFormula_50_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_150_formula_bound :
  (((139117709666745705377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 50) ∧
  (vasyuninBEntryFormula 1 50 ≤ ((139122213266455294623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_1_50_bounds
  have b_Vkh := cotangentSumVFormula_50_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_1_50_lower, cotangentSumVFormula_1_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_1_lower, cotangentSumVFormula_50_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_50_unfold :
    cotangentSumVFormula 3 50 =
      ((3/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 3 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_3_50_lower : ℚ := -1421512983909503079513 / 54975581388800000000
def cotangentSumVFormula_3_50_upper : ℚ := -1421512982809934420487 / 54975581388800000000
theorem cotangentSumVFormula_3_50_bounds :
  ((cotangentSumVFormula_3_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 50 ∧
  cotangentSumVFormula 3 50 ≤ ((cotangentSumVFormula_3_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_50_unfold]
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
  rw [cotangentSumVFormula_3_50_lower, cotangentSumVFormula_3_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_3_unfold :
    cotangentSumVFormula 50 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_50_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_50_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_50_3_bounds :
  ((cotangentSumVFormula_50_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 3 ∧
  cotangentSumVFormula 50 3 ≤ ((cotangentSumVFormula_50_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_50_3_lower, cotangentSumVFormula_50_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_350_formula_bound :
  (((57092687195215673001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 50) ∧
  (vasyuninBEntryFormula 3 50 ≤ ((57094938995042889499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_3_50_bounds
  have b_Vkh := cotangentSumVFormula_50_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_3_50_lower, cotangentSumVFormula_3_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_3_lower, cotangentSumVFormula_50_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_50_unfold :
    cotangentSumVFormula 7 50 =
      ((7/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 7 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_7_50_lower : ℚ := -638102941549256985763 / 54975581388800000000
def cotangentSumVFormula_7_50_upper : ℚ := -638102940449687545487 / 54975581388800000000
theorem cotangentSumVFormula_7_50_bounds :
  ((cotangentSumVFormula_7_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 50 ∧
  cotangentSumVFormula 7 50 ≤ ((cotangentSumVFormula_7_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_50_unfold]
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
  rw [cotangentSumVFormula_7_50_lower, cotangentSumVFormula_7_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_7_unfold :
    cotangentSumVFormula 50 7 =
      ((1/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_50_7_lower : ℚ := -3267942246185352841291 / 1759218604441600000000
def cotangentSumVFormula_50_7_upper : ℚ := -3267942211000966689959 / 1759218604441600000000
theorem cotangentSumVFormula_50_7_bounds :
  ((cotangentSumVFormula_50_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 7 ∧
  cotangentSumVFormula 50 7 ≤ ((cotangentSumVFormula_50_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_7_unfold]
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
  rw [cotangentSumVFormula_50_7_lower, cotangentSumVFormula_50_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_750_formula_bound :
  (((47632876954975548001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 50) ∧
  (vasyuninBEntryFormula 7 50 ≤ ((23817564377397499437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_7_50_bounds
  have b_Vkh := cotangentSumVFormula_50_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_7_50_lower, cotangentSumVFormula_7_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_7_lower, cotangentSumVFormula_50_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_50_unfold :
    cotangentSumVFormula 9 50 =
      ((9/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 9 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_9_50_lower : ℚ := -2095445223805484583677 / 219902325555200000000
def cotangentSumVFormula_9_50_upper : ℚ := -2095445219407209947573 / 219902325555200000000
theorem cotangentSumVFormula_9_50_bounds :
  ((cotangentSumVFormula_9_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 50 ∧
  cotangentSumVFormula 9 50 ≤ ((cotangentSumVFormula_9_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_50_unfold]
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
  rw [cotangentSumVFormula_9_50_lower, cotangentSumVFormula_9_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_9_unfold :
    cotangentSumVFormula 50 9 =
      ((5/9 : ℚ) : ℝ) * cotangentTermV 1 9    + 
      ((1/9 : ℚ) : ℝ) * cotangentTermV 2 9    + 
      ((6/9 : ℚ) : ℝ) * cotangentTermV 3 9    + 
      ((2/9 : ℚ) : ℝ) * cotangentTermV 4 9    + 
      ((7/9 : ℚ) : ℝ) * cotangentTermV 5 9    + 
      ((3/9 : ℚ) : ℝ) * cotangentTermV 6 9    + 
      ((8/9 : ℚ) : ℝ) * cotangentTermV 7 9    + 
      ((4/9 : ℚ) : ℝ) * cotangentTermV 8 9 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_9]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_50_9_lower : ℚ := -927378325653162216291 / 1759218604441600000000
def cotangentSumVFormula_50_9_upper : ℚ := -927378290468754971209 / 1759218604441600000000
theorem cotangentSumVFormula_50_9_bounds :
  ((cotangentSumVFormula_50_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 9 ∧
  cotangentSumVFormula 50 9 ≤ ((cotangentSumVFormula_50_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_9_unfold]
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
  rw [cotangentSumVFormula_50_9_lower, cotangentSumVFormula_50_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_950_formula_bound :
  (((89230488733750955377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 50) ∧
  (vasyuninBEntryFormula 9 50 ≤ ((89234992333387294623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_9_50_bounds
  have b_Vkh := cotangentSumVFormula_50_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_9_50_lower, cotangentSumVFormula_9_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_9_lower, cotangentSumVFormula_50_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_50_unfold :
    cotangentSumVFormula 11 50 =
      ((11/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 11 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_11_50_lower : ℚ := -2872061496646010182979 / 439804651110400000000
def cotangentSumVFormula_11_50_upper : ℚ := -2872061487849478098271 / 439804651110400000000
theorem cotangentSumVFormula_11_50_bounds :
  ((cotangentSumVFormula_11_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 50 ∧
  cotangentSumVFormula 11 50 ≤ ((cotangentSumVFormula_11_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_50_unfold]
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
  rw [cotangentSumVFormula_11_50_lower, cotangentSumVFormula_11_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_11_unfold :
    cotangentSumVFormula 50 11 =
      ((6/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_50_11_lower : ℚ := -3351142826950507635707 / 3518437208883200000000
def cotangentSumVFormula_50_11_upper : ℚ := -3351142756581654864293 / 3518437208883200000000
theorem cotangentSumVFormula_50_11_bounds :
  ((cotangentSumVFormula_50_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 11 ∧
  cotangentSumVFormula 50 11 ≤ ((cotangentSumVFormula_50_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_11_unfold]
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
  rw [cotangentSumVFormula_50_11_lower, cotangentSumVFormula_50_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1150_formula_bound :
  (((10582450890283929969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 50) ∧
  (vasyuninBEntryFormula 11 50 ≤ ((5291506920119120953 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_11_50_bounds
  have b_Vkh := cotangentSumVFormula_50_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_11_50_lower, cotangentSumVFormula_11_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_11_lower, cotangentSumVFormula_50_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_50_unfold :
    cotangentSumVFormula 13 50 =
      ((13/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 13 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_13_50_lower : ℚ := -1909037415010979114927 / 219902325555200000000
def cotangentSumVFormula_13_50_upper : ℚ := -1909037410612715416323 / 219902325555200000000
theorem cotangentSumVFormula_13_50_bounds :
  ((cotangentSumVFormula_13_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 50 ∧
  cotangentSumVFormula 13 50 ≤ ((cotangentSumVFormula_13_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_50_unfold]
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
  rw [cotangentSumVFormula_13_50_lower, cotangentSumVFormula_13_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_13_unfold :
    cotangentSumVFormula 50 13 =
      ((11/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_50_13_lower : ℚ := 1390755810232338254521 / 439804651110400000000
def cotangentSumVFormula_50_13_upper : ℚ := 1390755819028449245479 / 439804651110400000000
theorem cotangentSumVFormula_50_13_bounds :
  ((cotangentSumVFormula_50_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 13 ∧
  cotangentSumVFormula 50 13 ≤ ((cotangentSumVFormula_50_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_13_unfold]
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
  rw [cotangentSumVFormula_50_13_lower, cotangentSumVFormula_50_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1350_formula_bound :
  (((2539627381984775461 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 50) ∧
  (vasyuninBEntryFormula 13 50 ≤ ((2539768119473318289 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_13_50_bounds
  have b_Vkh := cotangentSumVFormula_50_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_13_50_lower, cotangentSumVFormula_13_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_13_lower, cotangentSumVFormula_50_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_50_unfold :
    cotangentSumVFormula 17 50 =
      ((17/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 17 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_17_50_lower : ℚ := -2541285945120854114927 / 219902325555200000000
def cotangentSumVFormula_17_50_upper : ℚ := -2541285940722597447573 / 219902325555200000000
theorem cotangentSumVFormula_17_50_bounds :
  ((cotangentSumVFormula_17_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 50 ∧
  cotangentSumVFormula 17 50 ≤ ((cotangentSumVFormula_17_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_50_unfold]
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
  rw [cotangentSumVFormula_17_50_lower, cotangentSumVFormula_17_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_17_unfold :
    cotangentSumVFormula 50 17 =
      ((16/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_50_17_lower : ℚ := 485596129413593014237 / 54975581388800000000
def cotangentSumVFormula_50_17_upper : ℚ := 485596130513109329513 / 54975581388800000000
theorem cotangentSumVFormula_50_17_bounds :
  ((cotangentSumVFormula_50_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 17 ∧
  cotangentSumVFormula 50 17 ≤ ((cotangentSumVFormula_50_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_17_unfold]
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
  rw [cotangentSumVFormula_50_17_lower, cotangentSumVFormula_50_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1750_formula_bound :
  (((38027591285841516751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 50) ∧
  (vasyuninBEntryFormula 17 50 ≤ ((38029843085657514499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_17_50_bounds
  have b_Vkh := cotangentSumVFormula_50_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_17_50_lower, cotangentSumVFormula_17_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_17_lower, cotangentSumVFormula_50_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_50_unfold :
    cotangentSumVFormula 19 50 =
      ((19/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((21/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 19 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_19_50_lower : ℚ := -1064559367947455495479 / 439804651110400000000
def cotangentSumVFormula_19_50_upper : ℚ := -1064559359150946848271 / 439804651110400000000
theorem cotangentSumVFormula_19_50_bounds :
  ((cotangentSumVFormula_19_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 50 ∧
  cotangentSumVFormula 19 50 ≤ ((cotangentSumVFormula_19_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_50_unfold]
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
  rw [cotangentSumVFormula_19_50_lower, cotangentSumVFormula_19_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_19_unfold :
    cotangentSumVFormula 50 19 =
      ((12/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_50_19_lower : ℚ := 2122920433318908096209 / 1759218604441600000000
def cotangentSumVFormula_50_19_upper : ℚ := 2122920468503440341291 / 1759218604441600000000
theorem cotangentSumVFormula_50_19_bounds :
  ((cotangentSumVFormula_50_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 19 ∧
  cotangentSumVFormula 50 19 ≤ ((cotangentSumVFormula_50_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_19_unfold]
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
  rw [cotangentSumVFormula_50_19_lower, cotangentSumVFormula_50_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1950_formula_bound :
  (((9007474330360961219 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 50) ∧
  (vasyuninBEntryFormula 19 50 ≤ ((2252009320078724539 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_19_50_bounds
  have b_Vkh := cotangentSumVFormula_50_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_19_50_lower, cotangentSumVFormula_19_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_19_lower, cotangentSumVFormula_50_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_21_50_unfold :
    cotangentSumVFormula 21 50 =
      ((21/50 : ℚ) : ℝ) * cotangentTermV 1 50    + 
      ((42/50 : ℚ) : ℝ) * cotangentTermV 2 50    + 
      ((13/50 : ℚ) : ℝ) * cotangentTermV 3 50    + 
      ((34/50 : ℚ) : ℝ) * cotangentTermV 4 50    + 
      ((5/50 : ℚ) : ℝ) * cotangentTermV 5 50    + 
      ((26/50 : ℚ) : ℝ) * cotangentTermV 6 50    + 
      ((47/50 : ℚ) : ℝ) * cotangentTermV 7 50    + 
      ((18/50 : ℚ) : ℝ) * cotangentTermV 8 50    + 
      ((39/50 : ℚ) : ℝ) * cotangentTermV 9 50    + 
      ((10/50 : ℚ) : ℝ) * cotangentTermV 10 50    + 
      ((31/50 : ℚ) : ℝ) * cotangentTermV 11 50    + 
      ((2/50 : ℚ) : ℝ) * cotangentTermV 12 50    + 
      ((23/50 : ℚ) : ℝ) * cotangentTermV 13 50    + 
      ((44/50 : ℚ) : ℝ) * cotangentTermV 14 50    + 
      ((15/50 : ℚ) : ℝ) * cotangentTermV 15 50    + 
      ((36/50 : ℚ) : ℝ) * cotangentTermV 16 50    + 
      ((7/50 : ℚ) : ℝ) * cotangentTermV 17 50    + 
      ((28/50 : ℚ) : ℝ) * cotangentTermV 18 50    + 
      ((49/50 : ℚ) : ℝ) * cotangentTermV 19 50    + 
      ((20/50 : ℚ) : ℝ) * cotangentTermV 20 50    + 
      ((41/50 : ℚ) : ℝ) * cotangentTermV 21 50    + 
      ((12/50 : ℚ) : ℝ) * cotangentTermV 22 50    + 
      ((33/50 : ℚ) : ℝ) * cotangentTermV 23 50    + 
      ((4/50 : ℚ) : ℝ) * cotangentTermV 24 50    + 
      ((25/50 : ℚ) : ℝ) * cotangentTermV 25 50    + 
      ((46/50 : ℚ) : ℝ) * cotangentTermV 26 50    + 
      ((17/50 : ℚ) : ℝ) * cotangentTermV 27 50    + 
      ((38/50 : ℚ) : ℝ) * cotangentTermV 28 50    + 
      ((9/50 : ℚ) : ℝ) * cotangentTermV 29 50    + 
      ((30/50 : ℚ) : ℝ) * cotangentTermV 30 50    + 
      ((1/50 : ℚ) : ℝ) * cotangentTermV 31 50    + 
      ((22/50 : ℚ) : ℝ) * cotangentTermV 32 50    + 
      ((43/50 : ℚ) : ℝ) * cotangentTermV 33 50    + 
      ((14/50 : ℚ) : ℝ) * cotangentTermV 34 50    + 
      ((35/50 : ℚ) : ℝ) * cotangentTermV 35 50    + 
      ((6/50 : ℚ) : ℝ) * cotangentTermV 36 50    + 
      ((27/50 : ℚ) : ℝ) * cotangentTermV 37 50    + 
      ((48/50 : ℚ) : ℝ) * cotangentTermV 38 50    + 
      ((19/50 : ℚ) : ℝ) * cotangentTermV 39 50    + 
      ((40/50 : ℚ) : ℝ) * cotangentTermV 40 50    + 
      ((11/50 : ℚ) : ℝ) * cotangentTermV 41 50    + 
      ((32/50 : ℚ) : ℝ) * cotangentTermV 42 50    + 
      ((3/50 : ℚ) : ℝ) * cotangentTermV 43 50    + 
      ((24/50 : ℚ) : ℝ) * cotangentTermV 44 50    + 
      ((45/50 : ℚ) : ℝ) * cotangentTermV 45 50    + 
      ((16/50 : ℚ) : ℝ) * cotangentTermV 46 50    + 
      ((37/50 : ℚ) : ℝ) * cotangentTermV 47 50    + 
      ((8/50 : ℚ) : ℝ) * cotangentTermV 48 50    + 
      ((29/50 : ℚ) : ℝ) * cotangentTermV 49 50 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_50]
  have hf_1 : Int.fract (((1 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((21/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((42/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((13/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((34/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((5/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((26/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((47/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((18/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((39/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((10/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((31/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((2/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((23/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((44/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((15/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((36/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((7/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((28/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((49/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((20/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((41/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((12/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((33/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((4/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((25/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((46/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((17/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((38/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((9/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((30/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((1/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((22/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((43/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((14/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((35/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((6/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((27/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((48/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((19/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((40/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((11/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((32/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((3/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((24/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((45/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((16/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((37/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_48 : Int.fract (((48 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((8/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_49 : Int.fract (((49 * 21 : ℕ) : ℝ) / ((50 : ℕ) : ℝ)) = ((29/50 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47, hf_48, hf_49]
  try ring

def cotangentSumVFormula_21_50_lower : ℚ := 2332086127392908770543 / 3518437208883200000000
def cotangentSumVFormula_21_50_upper : ℚ := 2332086197764828729457 / 3518437208883200000000
theorem cotangentSumVFormula_21_50_bounds :
  ((cotangentSumVFormula_21_50_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 21 50 ∧
  cotangentSumVFormula 21 50 ≤ ((cotangentSumVFormula_21_50_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_21_50_unfold]
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
  rw [cotangentSumVFormula_21_50_lower, cotangentSumVFormula_21_50_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_50_21_unfold :
    cotangentSumVFormula 50 21 =
      ((8/21 : ℚ) : ℝ) * cotangentTermV 1 21    + 
      ((16/21 : ℚ) : ℝ) * cotangentTermV 2 21    + 
      ((3/21 : ℚ) : ℝ) * cotangentTermV 3 21    + 
      ((11/21 : ℚ) : ℝ) * cotangentTermV 4 21    + 
      ((19/21 : ℚ) : ℝ) * cotangentTermV 5 21    + 
      ((6/21 : ℚ) : ℝ) * cotangentTermV 6 21    + 
      ((14/21 : ℚ) : ℝ) * cotangentTermV 7 21    + 
      ((1/21 : ℚ) : ℝ) * cotangentTermV 8 21    + 
      ((9/21 : ℚ) : ℝ) * cotangentTermV 9 21    + 
      ((17/21 : ℚ) : ℝ) * cotangentTermV 10 21    + 
      ((4/21 : ℚ) : ℝ) * cotangentTermV 11 21    + 
      ((12/21 : ℚ) : ℝ) * cotangentTermV 12 21    + 
      ((20/21 : ℚ) : ℝ) * cotangentTermV 13 21    + 
      ((7/21 : ℚ) : ℝ) * cotangentTermV 14 21    + 
      ((15/21 : ℚ) : ℝ) * cotangentTermV 15 21    + 
      ((2/21 : ℚ) : ℝ) * cotangentTermV 16 21    + 
      ((10/21 : ℚ) : ℝ) * cotangentTermV 17 21    + 
      ((18/21 : ℚ) : ℝ) * cotangentTermV 18 21    + 
      ((5/21 : ℚ) : ℝ) * cotangentTermV 19 21    + 
      ((13/21 : ℚ) : ℝ) * cotangentTermV 20 21 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_21]
  have hf_1 : Int.fract (((1 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((8/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((16/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((3/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((11/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((19/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((6/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((14/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((1/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((9/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((17/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((4/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((12/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((20/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((7/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((15/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((2/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((10/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((18/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((5/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 50 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((13/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20]
  try ring

def cotangentSumVFormula_50_21_lower : ℚ := -1606286422726598935041 / 1759218604441600000000
def cotangentSumVFormula_50_21_upper : ℚ := -1606286387542033877459 / 1759218604441600000000
theorem cotangentSumVFormula_50_21_bounds :
  ((cotangentSumVFormula_50_21_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 50 21 ∧
  cotangentSumVFormula 50 21 ≤ ((cotangentSumVFormula_50_21_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_50_21_unfold]
  have b_cot_1 := cot_pi_1_21_bounds
  simp only [cot_pi_1_21_lower, cot_pi_1_21_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_21_bounds
  simp only [cot_pi_2_21_lower, cot_pi_2_21_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_21_bounds
  simp only [cot_pi_3_21_lower, cot_pi_3_21_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_21_bounds
  simp only [cot_pi_4_21_lower, cot_pi_4_21_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_21_bounds
  simp only [cot_pi_5_21_lower, cot_pi_5_21_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_21_bounds
  simp only [cot_pi_6_21_lower, cot_pi_6_21_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_21_bounds
  simp only [cot_pi_7_21_lower, cot_pi_7_21_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_21_bounds
  simp only [cot_pi_8_21_lower, cot_pi_8_21_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_21_bounds
  simp only [cot_pi_9_21_lower, cot_pi_9_21_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_21_bounds
  simp only [cot_pi_10_21_lower, cot_pi_10_21_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_21_bounds
  simp only [cot_pi_11_21_lower, cot_pi_11_21_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_21_bounds
  simp only [cot_pi_12_21_lower, cot_pi_12_21_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_21_bounds
  simp only [cot_pi_13_21_lower, cot_pi_13_21_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_21_bounds
  simp only [cot_pi_14_21_lower, cot_pi_14_21_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_21_bounds
  simp only [cot_pi_15_21_lower, cot_pi_15_21_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_21_bounds
  simp only [cot_pi_16_21_lower, cot_pi_16_21_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_21_bounds
  simp only [cot_pi_17_21_lower, cot_pi_17_21_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_21_bounds
  simp only [cot_pi_18_21_lower, cot_pi_18_21_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_21_bounds
  simp only [cot_pi_19_21_lower, cot_pi_19_21_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_21_bounds
  simp only [cot_pi_20_21_lower, cot_pi_20_21_upper] at b_cot_20
  rw [cotangentSumVFormula_50_21_lower, cotangentSumVFormula_50_21_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2150_formula_bound :
  (((139683484307136645129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 21 50) ∧
  (vasyuninBEntryFormula 21 50 ≤ ((139692491506398698621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 21 50 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log21 := prim_log_21_bounds
  have b_log50 := prim_log_50_bounds
  have b_Vhk := cotangentSumVFormula_21_50_bounds
  have b_Vkh := cotangentSumVFormula_50_21_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_21_lower, prim_log_21_upper] at b_log21
  simp only [prim_log_50_lower, prim_log_50_upper] at b_log50
  simp only [cotangentSumVFormula_21_50_lower, cotangentSumVFormula_21_50_upper] at b_Vhk
  simp only [cotangentSumVFormula_50_21_lower, cotangentSumVFormula_50_21_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
