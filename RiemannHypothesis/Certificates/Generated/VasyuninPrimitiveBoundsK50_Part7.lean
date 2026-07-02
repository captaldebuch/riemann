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

theorem cotangentSumVFormula_23_45_unfold :
    cotangentSumVFormula 23 45 =
      ((23/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 23 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_23_45_lower : ℚ := -1476987337410491705901 / 109951162777600000000
def cotangentSumVFormula_23_45_upper : ℚ := -369246833802846702431 / 27487790694400000000
theorem cotangentSumVFormula_23_45_bounds :
  ((cotangentSumVFormula_23_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 45 ∧
  cotangentSumVFormula 23 45 ≤ ((cotangentSumVFormula_23_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_45_unfold]
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
  rw [cotangentSumVFormula_23_45_lower, cotangentSumVFormula_23_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_23_unfold :
    cotangentSumVFormula 45 23 =
      ((22/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_45_23_lower : ℚ := 3089186429796141197573 / 219902325555200000000
def cotangentSumVFormula_45_23_upper : ℚ := 3089186434194219739927 / 219902325555200000000
theorem cotangentSumVFormula_45_23_bounds :
  ((cotangentSumVFormula_45_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 23 ∧
  cotangentSumVFormula 45 23 ≤ ((cotangentSumVFormula_45_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_23_unfold]
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
  rw [cotangentSumVFormula_45_23_lower, cotangentSumVFormula_45_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2345_formula_bound :
  (((75087761911612142877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 45) ∧
  (vasyuninBEntryFormula 23 45 ≤ ((75092265511242825873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_23_45_bounds
  have b_Vkh := cotangentSumVFormula_45_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_23_45_lower, cotangentSumVFormula_23_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_23_lower, cotangentSumVFormula_45_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_26_45_unfold :
    cotangentSumVFormula 26 45 =
      ((26/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 26 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_26_45_lower : ℚ := -112151587088539362151 / 109951162777600000000
def cotangentSumVFormula_26_45_upper : ℚ := -56075792444716451737 / 54975581388800000000
theorem cotangentSumVFormula_26_45_bounds :
  ((cotangentSumVFormula_26_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 26 45 ∧
  cotangentSumVFormula 26 45 ≤ ((cotangentSumVFormula_26_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_26_45_unfold]
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
  rw [cotangentSumVFormula_26_45_lower, cotangentSumVFormula_26_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_26_unfold :
    cotangentSumVFormula 45 26 =
      ((19/26 : ℚ) : ℝ) * cotangentTermV 1 26    + 
      ((12/26 : ℚ) : ℝ) * cotangentTermV 2 26    + 
      ((5/26 : ℚ) : ℝ) * cotangentTermV 3 26    + 
      ((24/26 : ℚ) : ℝ) * cotangentTermV 4 26    + 
      ((17/26 : ℚ) : ℝ) * cotangentTermV 5 26    + 
      ((10/26 : ℚ) : ℝ) * cotangentTermV 6 26    + 
      ((3/26 : ℚ) : ℝ) * cotangentTermV 7 26    + 
      ((22/26 : ℚ) : ℝ) * cotangentTermV 8 26    + 
      ((15/26 : ℚ) : ℝ) * cotangentTermV 9 26    + 
      ((8/26 : ℚ) : ℝ) * cotangentTermV 10 26    + 
      ((1/26 : ℚ) : ℝ) * cotangentTermV 11 26    + 
      ((20/26 : ℚ) : ℝ) * cotangentTermV 12 26    + 
      ((13/26 : ℚ) : ℝ) * cotangentTermV 13 26    + 
      ((6/26 : ℚ) : ℝ) * cotangentTermV 14 26    + 
      ((25/26 : ℚ) : ℝ) * cotangentTermV 15 26    + 
      ((18/26 : ℚ) : ℝ) * cotangentTermV 16 26    + 
      ((11/26 : ℚ) : ℝ) * cotangentTermV 17 26    + 
      ((4/26 : ℚ) : ℝ) * cotangentTermV 18 26    + 
      ((23/26 : ℚ) : ℝ) * cotangentTermV 19 26    + 
      ((16/26 : ℚ) : ℝ) * cotangentTermV 20 26    + 
      ((9/26 : ℚ) : ℝ) * cotangentTermV 21 26    + 
      ((2/26 : ℚ) : ℝ) * cotangentTermV 22 26    + 
      ((21/26 : ℚ) : ℝ) * cotangentTermV 23 26    + 
      ((14/26 : ℚ) : ℝ) * cotangentTermV 24 26    + 
      ((7/26 : ℚ) : ℝ) * cotangentTermV 25 26 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_26]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((19/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((12/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((5/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((24/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((17/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((10/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((3/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((22/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((15/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((8/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((1/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((20/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((13/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((6/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((25/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((18/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((11/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((4/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((23/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((16/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((9/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((2/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((21/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((14/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((7/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25]
  try ring

def cotangentSumVFormula_45_26_lower : ℚ := 2843786636867027680917 / 879609302220800000000
def cotangentSumVFormula_45_26_upper : ℚ := 2843786654459380131583 / 879609302220800000000
theorem cotangentSumVFormula_45_26_bounds :
  ((cotangentSumVFormula_45_26_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 26 ∧
  cotangentSumVFormula 45 26 ≤ ((cotangentSumVFormula_45_26_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_26_unfold]
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
  rw [cotangentSumVFormula_45_26_lower, cotangentSumVFormula_45_26_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2645_formula_bound :
  (((138821585828187020129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 26 45) ∧
  (vasyuninBEntryFormula 26 45 ≤ ((138830593027447886121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 26 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log26 := prim_log_26_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_26_45_bounds
  have b_Vkh := cotangentSumVFormula_45_26_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_26_lower, prim_log_26_upper] at b_log26
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_26_45_lower, cotangentSumVFormula_26_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_26_lower, cotangentSumVFormula_45_26_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_28_45_unfold :
    cotangentSumVFormula 28 45 =
      ((28/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 28 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_28_45_lower : ℚ := 708216085162851353823 / 219902325555200000000
def cotangentSumVFormula_28_45_upper : ℚ := 354108044780527643401 / 109951162777600000000
theorem cotangentSumVFormula_28_45_bounds :
  ((cotangentSumVFormula_28_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 28 45 ∧
  cotangentSumVFormula 28 45 ≤ ((cotangentSumVFormula_28_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_28_45_unfold]
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
  rw [cotangentSumVFormula_28_45_lower, cotangentSumVFormula_28_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_28_unfold :
    cotangentSumVFormula 45 28 =
      ((17/28 : ℚ) : ℝ) * cotangentTermV 1 28    + 
      ((6/28 : ℚ) : ℝ) * cotangentTermV 2 28    + 
      ((23/28 : ℚ) : ℝ) * cotangentTermV 3 28    + 
      ((12/28 : ℚ) : ℝ) * cotangentTermV 4 28    + 
      ((1/28 : ℚ) : ℝ) * cotangentTermV 5 28    + 
      ((18/28 : ℚ) : ℝ) * cotangentTermV 6 28    + 
      ((7/28 : ℚ) : ℝ) * cotangentTermV 7 28    + 
      ((24/28 : ℚ) : ℝ) * cotangentTermV 8 28    + 
      ((13/28 : ℚ) : ℝ) * cotangentTermV 9 28    + 
      ((2/28 : ℚ) : ℝ) * cotangentTermV 10 28    + 
      ((19/28 : ℚ) : ℝ) * cotangentTermV 11 28    + 
      ((8/28 : ℚ) : ℝ) * cotangentTermV 12 28    + 
      ((25/28 : ℚ) : ℝ) * cotangentTermV 13 28    + 
      ((14/28 : ℚ) : ℝ) * cotangentTermV 14 28    + 
      ((3/28 : ℚ) : ℝ) * cotangentTermV 15 28    + 
      ((20/28 : ℚ) : ℝ) * cotangentTermV 16 28    + 
      ((9/28 : ℚ) : ℝ) * cotangentTermV 17 28    + 
      ((26/28 : ℚ) : ℝ) * cotangentTermV 18 28    + 
      ((15/28 : ℚ) : ℝ) * cotangentTermV 19 28    + 
      ((4/28 : ℚ) : ℝ) * cotangentTermV 20 28    + 
      ((21/28 : ℚ) : ℝ) * cotangentTermV 21 28    + 
      ((10/28 : ℚ) : ℝ) * cotangentTermV 22 28    + 
      ((27/28 : ℚ) : ℝ) * cotangentTermV 23 28    + 
      ((16/28 : ℚ) : ℝ) * cotangentTermV 24 28    + 
      ((5/28 : ℚ) : ℝ) * cotangentTermV 25 28    + 
      ((22/28 : ℚ) : ℝ) * cotangentTermV 26 28    + 
      ((11/28 : ℚ) : ℝ) * cotangentTermV 27 28 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_28]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((17/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((6/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((23/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((12/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((1/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((18/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((7/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((24/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((13/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((2/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((19/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((8/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((25/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((14/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((3/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((20/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((9/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((26/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((15/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((4/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((21/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((10/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((27/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((16/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((5/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((22/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((11/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27]
  try ring

def cotangentSumVFormula_45_28_lower : ℚ := -3188508583379400037039 / 7036874417766400000000
def cotangentSumVFormula_45_28_upper : ℚ := -3188508442640168712961 / 7036874417766400000000
theorem cotangentSumVFormula_45_28_bounds :
  ((cotangentSumVFormula_45_28_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 28 ∧
  cotangentSumVFormula 45 28 ≤ ((cotangentSumVFormula_45_28_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_28_unfold]
  have b_cot_1 := cot_pi_1_28_bounds
  simp only [cot_pi_1_28_lower, cot_pi_1_28_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_28_bounds
  simp only [cot_pi_2_28_lower, cot_pi_2_28_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_28_bounds
  simp only [cot_pi_3_28_lower, cot_pi_3_28_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_28_bounds
  simp only [cot_pi_4_28_lower, cot_pi_4_28_upper] at b_cot_4
  have b_cot_5 := cot_pi_5_28_bounds
  simp only [cot_pi_5_28_lower, cot_pi_5_28_upper] at b_cot_5
  have b_cot_6 := cot_pi_6_28_bounds
  simp only [cot_pi_6_28_lower, cot_pi_6_28_upper] at b_cot_6
  have b_cot_7 := cot_pi_7_28_bounds
  simp only [cot_pi_7_28_lower, cot_pi_7_28_upper] at b_cot_7
  have b_cot_8 := cot_pi_8_28_bounds
  simp only [cot_pi_8_28_lower, cot_pi_8_28_upper] at b_cot_8
  have b_cot_9 := cot_pi_9_28_bounds
  simp only [cot_pi_9_28_lower, cot_pi_9_28_upper] at b_cot_9
  have b_cot_10 := cot_pi_10_28_bounds
  simp only [cot_pi_10_28_lower, cot_pi_10_28_upper] at b_cot_10
  have b_cot_11 := cot_pi_11_28_bounds
  simp only [cot_pi_11_28_lower, cot_pi_11_28_upper] at b_cot_11
  have b_cot_12 := cot_pi_12_28_bounds
  simp only [cot_pi_12_28_lower, cot_pi_12_28_upper] at b_cot_12
  have b_cot_13 := cot_pi_13_28_bounds
  simp only [cot_pi_13_28_lower, cot_pi_13_28_upper] at b_cot_13
  have b_cot_14 := cot_pi_14_28_bounds
  simp only [cot_pi_14_28_lower, cot_pi_14_28_upper] at b_cot_14
  have b_cot_15 := cot_pi_15_28_bounds
  simp only [cot_pi_15_28_lower, cot_pi_15_28_upper] at b_cot_15
  have b_cot_16 := cot_pi_16_28_bounds
  simp only [cot_pi_16_28_lower, cot_pi_16_28_upper] at b_cot_16
  have b_cot_17 := cot_pi_17_28_bounds
  simp only [cot_pi_17_28_lower, cot_pi_17_28_upper] at b_cot_17
  have b_cot_18 := cot_pi_18_28_bounds
  simp only [cot_pi_18_28_lower, cot_pi_18_28_upper] at b_cot_18
  have b_cot_19 := cot_pi_19_28_bounds
  simp only [cot_pi_19_28_lower, cot_pi_19_28_upper] at b_cot_19
  have b_cot_20 := cot_pi_20_28_bounds
  simp only [cot_pi_20_28_lower, cot_pi_20_28_upper] at b_cot_20
  have b_cot_21 := cot_pi_21_28_bounds
  simp only [cot_pi_21_28_lower, cot_pi_21_28_upper] at b_cot_21
  have b_cot_22 := cot_pi_22_28_bounds
  simp only [cot_pi_22_28_lower, cot_pi_22_28_upper] at b_cot_22
  have b_cot_23 := cot_pi_23_28_bounds
  simp only [cot_pi_23_28_lower, cot_pi_23_28_upper] at b_cot_23
  have b_cot_24 := cot_pi_24_28_bounds
  simp only [cot_pi_24_28_lower, cot_pi_24_28_upper] at b_cot_24
  have b_cot_25 := cot_pi_25_28_bounds
  simp only [cot_pi_25_28_lower, cot_pi_25_28_upper] at b_cot_25
  have b_cot_26 := cot_pi_26_28_bounds
  simp only [cot_pi_26_28_lower, cot_pi_26_28_upper] at b_cot_26
  have b_cot_27 := cot_pi_27_28_bounds
  simp only [cot_pi_27_28_lower, cot_pi_27_28_upper] at b_cot_27
  rw [cotangentSumVFormula_45_28_lower, cotangentSumVFormula_45_28_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2845_formula_bound :
  (((134510516861768645129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 28 45) ∧
  (vasyuninBEntryFormula 28 45 ≤ ((134519524061029198621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 28 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log28 := prim_log_28_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_28_45_bounds
  have b_Vkh := cotangentSumVFormula_45_28_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_28_lower, prim_log_28_upper] at b_log28
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_28_45_lower, cotangentSumVFormula_28_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_28_lower, cotangentSumVFormula_45_28_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_45_unfold :
    cotangentSumVFormula 29 45 =
      ((29/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 29 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_29_45_lower : ℚ := 2053485132865913254521 / 439804651110400000000
def cotangentSumVFormula_29_45_upper : ℚ := 2053485141662317214229 / 439804651110400000000
theorem cotangentSumVFormula_29_45_bounds :
  ((cotangentSumVFormula_29_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 45 ∧
  cotangentSumVFormula 29 45 ≤ ((cotangentSumVFormula_29_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_45_unfold]
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
  rw [cotangentSumVFormula_29_45_lower, cotangentSumVFormula_29_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_29_unfold :
    cotangentSumVFormula 45 29 =
      ((16/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_45_29_lower : ℚ := -760525778336925807979 / 439804651110400000000
def cotangentSumVFormula_45_29_upper : ℚ := -760525769540721848271 / 439804651110400000000
theorem cotangentSumVFormula_45_29_bounds :
  ((cotangentSumVFormula_45_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 29 ∧
  cotangentSumVFormula 45 29 ≤ ((cotangentSumVFormula_45_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_29_unfold]
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
  rw [cotangentSumVFormula_45_29_lower, cotangentSumVFormula_45_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2945_formula_bound :
  (((132900463054655551379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 45) ∧
  (vasyuninBEntryFormula 29 45 ≤ ((132909470253915886121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_29_45_bounds
  have b_Vkh := cotangentSumVFormula_45_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_29_45_lower, cotangentSumVFormula_29_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_29_lower, cotangentSumVFormula_45_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_45_unfold :
    cotangentSumVFormula 31 45 =
      ((31/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 31 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_31_45_lower : ℚ := 1268681153168424502459 / 1759218604441600000000
def cotangentSumVFormula_31_45_upper : ℚ := 1268681188354028622541 / 1759218604441600000000
theorem cotangentSumVFormula_31_45_bounds :
  ((cotangentSumVFormula_31_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 45 ∧
  cotangentSumVFormula 31 45 ≤ ((cotangentSumVFormula_31_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_45_unfold]
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
  rw [cotangentSumVFormula_31_45_lower, cotangentSumVFormula_31_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_31_unfold :
    cotangentSumVFormula 45 31 =
      ((14/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_45_31_lower : ℚ := 2236310803950968305917 / 879609302220800000000
def cotangentSumVFormula_45_31_upper : ℚ := 2236310821543423881583 / 879609302220800000000
theorem cotangentSumVFormula_45_31_bounds :
  ((cotangentSumVFormula_45_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 31 ∧
  cotangentSumVFormula 45 31 ≤ ((cotangentSumVFormula_45_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_31_unfold]
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
  rw [cotangentSumVFormula_45_31_lower, cotangentSumVFormula_45_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3145_formula_bound :
  (((129679890634112582629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 45) ∧
  (vasyuninBEntryFormula 31 45 ≤ ((129688897833372823621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_31_45_bounds
  have b_Vkh := cotangentSumVFormula_45_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_31_45_lower, cotangentSumVFormula_31_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_31_lower, cotangentSumVFormula_45_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_32_45_unfold :
    cotangentSumVFormula 32 45 =
      ((32/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 32 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_32_45_lower : ℚ := 2299112708197867160771 / 439804651110400000000
def cotangentSumVFormula_32_45_upper : ℚ := 2299112716994255495479 / 439804651110400000000
theorem cotangentSumVFormula_32_45_bounds :
  ((cotangentSumVFormula_32_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 32 45 ∧
  cotangentSumVFormula 32 45 ≤ ((cotangentSumVFormula_32_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_32_45_unfold]
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
  rw [cotangentSumVFormula_32_45_lower, cotangentSumVFormula_32_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_32_unfold :
    cotangentSumVFormula 45 32 =
      ((13/32 : ℚ) : ℝ) * cotangentTermV 1 32    + 
      ((26/32 : ℚ) : ℝ) * cotangentTermV 2 32    + 
      ((7/32 : ℚ) : ℝ) * cotangentTermV 3 32    + 
      ((20/32 : ℚ) : ℝ) * cotangentTermV 4 32    + 
      ((1/32 : ℚ) : ℝ) * cotangentTermV 5 32    + 
      ((14/32 : ℚ) : ℝ) * cotangentTermV 6 32    + 
      ((27/32 : ℚ) : ℝ) * cotangentTermV 7 32    + 
      ((8/32 : ℚ) : ℝ) * cotangentTermV 8 32    + 
      ((21/32 : ℚ) : ℝ) * cotangentTermV 9 32    + 
      ((2/32 : ℚ) : ℝ) * cotangentTermV 10 32    + 
      ((15/32 : ℚ) : ℝ) * cotangentTermV 11 32    + 
      ((28/32 : ℚ) : ℝ) * cotangentTermV 12 32    + 
      ((9/32 : ℚ) : ℝ) * cotangentTermV 13 32    + 
      ((22/32 : ℚ) : ℝ) * cotangentTermV 14 32    + 
      ((3/32 : ℚ) : ℝ) * cotangentTermV 15 32    + 
      ((16/32 : ℚ) : ℝ) * cotangentTermV 16 32    + 
      ((29/32 : ℚ) : ℝ) * cotangentTermV 17 32    + 
      ((10/32 : ℚ) : ℝ) * cotangentTermV 18 32    + 
      ((23/32 : ℚ) : ℝ) * cotangentTermV 19 32    + 
      ((4/32 : ℚ) : ℝ) * cotangentTermV 20 32    + 
      ((17/32 : ℚ) : ℝ) * cotangentTermV 21 32    + 
      ((30/32 : ℚ) : ℝ) * cotangentTermV 22 32    + 
      ((11/32 : ℚ) : ℝ) * cotangentTermV 23 32    + 
      ((24/32 : ℚ) : ℝ) * cotangentTermV 24 32    + 
      ((5/32 : ℚ) : ℝ) * cotangentTermV 25 32    + 
      ((18/32 : ℚ) : ℝ) * cotangentTermV 26 32    + 
      ((31/32 : ℚ) : ℝ) * cotangentTermV 27 32    + 
      ((12/32 : ℚ) : ℝ) * cotangentTermV 28 32    + 
      ((25/32 : ℚ) : ℝ) * cotangentTermV 29 32    + 
      ((6/32 : ℚ) : ℝ) * cotangentTermV 30 32    + 
      ((19/32 : ℚ) : ℝ) * cotangentTermV 31 32 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_32]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((13/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((26/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((7/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((20/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((1/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((14/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((27/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((8/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((21/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((2/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((15/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((28/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((9/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((22/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((3/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((16/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((29/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((10/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((23/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((4/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((17/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((30/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((11/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((24/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((5/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((18/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((31/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((12/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((25/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((6/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((19/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31]
  try ring

def cotangentSumVFormula_45_32_lower : ℚ := -3174991683376863778791 / 1759218604441600000000
def cotangentSumVFormula_45_32_upper : ℚ := -3174991648192067471209 / 1759218604441600000000
theorem cotangentSumVFormula_45_32_bounds :
  ((cotangentSumVFormula_45_32_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 32 ∧
  cotangentSumVFormula 45 32 ≤ ((cotangentSumVFormula_45_32_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_32_unfold]
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
  rw [cotangentSumVFormula_45_32_lower, cotangentSumVFormula_45_32_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3245_formula_bound :
  (((128044450420876020129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 32 45) ∧
  (vasyuninBEntryFormula 32 45 ≤ ((128053457620135573621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 32 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log32 := prim_log_32_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_32_45_bounds
  have b_Vkh := cotangentSumVFormula_45_32_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_32_lower, prim_log_32_upper] at b_log32
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_32_45_lower, cotangentSumVFormula_32_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_32_lower, cotangentSumVFormula_45_32_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_34_45_unfold :
    cotangentSumVFormula 34 45 =
      ((34/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 34 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_34_45_lower : ℚ := 2436123191119694814959 / 1759218604441600000000
def cotangentSumVFormula_34_45_upper : ℚ := 2436123226305220810041 / 1759218604441600000000
theorem cotangentSumVFormula_34_45_bounds :
  ((cotangentSumVFormula_34_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 34 45 ∧
  cotangentSumVFormula 34 45 ≤ ((cotangentSumVFormula_34_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_34_45_unfold]
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
  rw [cotangentSumVFormula_34_45_lower, cotangentSumVFormula_34_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_34_unfold :
    cotangentSumVFormula 45 34 =
      ((11/34 : ℚ) : ℝ) * cotangentTermV 1 34    + 
      ((22/34 : ℚ) : ℝ) * cotangentTermV 2 34    + 
      ((33/34 : ℚ) : ℝ) * cotangentTermV 3 34    + 
      ((10/34 : ℚ) : ℝ) * cotangentTermV 4 34    + 
      ((21/34 : ℚ) : ℝ) * cotangentTermV 5 34    + 
      ((32/34 : ℚ) : ℝ) * cotangentTermV 6 34    + 
      ((9/34 : ℚ) : ℝ) * cotangentTermV 7 34    + 
      ((20/34 : ℚ) : ℝ) * cotangentTermV 8 34    + 
      ((31/34 : ℚ) : ℝ) * cotangentTermV 9 34    + 
      ((8/34 : ℚ) : ℝ) * cotangentTermV 10 34    + 
      ((19/34 : ℚ) : ℝ) * cotangentTermV 11 34    + 
      ((30/34 : ℚ) : ℝ) * cotangentTermV 12 34    + 
      ((7/34 : ℚ) : ℝ) * cotangentTermV 13 34    + 
      ((18/34 : ℚ) : ℝ) * cotangentTermV 14 34    + 
      ((29/34 : ℚ) : ℝ) * cotangentTermV 15 34    + 
      ((6/34 : ℚ) : ℝ) * cotangentTermV 16 34    + 
      ((17/34 : ℚ) : ℝ) * cotangentTermV 17 34    + 
      ((28/34 : ℚ) : ℝ) * cotangentTermV 18 34    + 
      ((5/34 : ℚ) : ℝ) * cotangentTermV 19 34    + 
      ((16/34 : ℚ) : ℝ) * cotangentTermV 20 34    + 
      ((27/34 : ℚ) : ℝ) * cotangentTermV 21 34    + 
      ((4/34 : ℚ) : ℝ) * cotangentTermV 22 34    + 
      ((15/34 : ℚ) : ℝ) * cotangentTermV 23 34    + 
      ((26/34 : ℚ) : ℝ) * cotangentTermV 24 34    + 
      ((3/34 : ℚ) : ℝ) * cotangentTermV 25 34    + 
      ((14/34 : ℚ) : ℝ) * cotangentTermV 26 34    + 
      ((25/34 : ℚ) : ℝ) * cotangentTermV 27 34    + 
      ((2/34 : ℚ) : ℝ) * cotangentTermV 28 34    + 
      ((13/34 : ℚ) : ℝ) * cotangentTermV 29 34    + 
      ((24/34 : ℚ) : ℝ) * cotangentTermV 30 34    + 
      ((1/34 : ℚ) : ℝ) * cotangentTermV 31 34    + 
      ((12/34 : ℚ) : ℝ) * cotangentTermV 32 34    + 
      ((23/34 : ℚ) : ℝ) * cotangentTermV 33 34 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_34]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((11/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((22/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((33/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((10/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((21/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((32/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((9/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((20/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((31/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((8/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((19/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((30/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((7/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((18/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((29/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((6/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((17/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((28/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((5/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((16/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((27/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((4/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((15/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((26/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((3/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((14/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((25/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((2/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((13/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((24/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((1/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((12/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((23/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33]
  try ring

def cotangentSumVFormula_45_34_lower : ℚ := 471245874538221666323 / 219902325555200000000
def cotangentSumVFormula_45_34_upper : ℚ := 471245878936361927427 / 219902325555200000000
theorem cotangentSumVFormula_45_34_bounds :
  ((cotangentSumVFormula_45_34_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 34 ∧
  cotangentSumVFormula 45 34 ≤ ((cotangentSumVFormula_45_34_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_34_unfold]
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
  rw [cotangentSumVFormula_45_34_lower, cotangentSumVFormula_45_34_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3445_formula_bound :
  (((125722698383822488879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 34 45) ∧
  (vasyuninBEntryFormula 34 45 ≤ ((125731705583082573621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 34 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log34 := prim_log_34_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_34_45_bounds
  have b_Vkh := cotangentSumVFormula_45_34_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_34_lower, prim_log_34_upper] at b_log34
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_34_45_lower, cotangentSumVFormula_34_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_34_lower, cotangentSumVFormula_45_34_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_45_unfold :
    cotangentSumVFormula 37 45 =
      ((37/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 37 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_37_45_lower : ℚ := 1056744354359695012849 / 109951162777600000000
def cotangentSumVFormula_37_45_upper : ℚ := 132093044569847937847 / 13743895347200000000
theorem cotangentSumVFormula_37_45_bounds :
  ((cotangentSumVFormula_37_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 45 ∧
  cotangentSumVFormula 37 45 ≤ ((cotangentSumVFormula_37_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_45_unfold]
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
  rw [cotangentSumVFormula_37_45_lower, cotangentSumVFormula_37_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_37_unfold :
    cotangentSumVFormula 45 37 =
      ((8/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_45_37_lower : ℚ := -671831399940639362151 / 109951162777600000000
def cotangentSumVFormula_45_37_upper : ℚ := -671831397741572356599 / 109951162777600000000
theorem cotangentSumVFormula_45_37_bounds :
  ((cotangentSumVFormula_45_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 37 ∧
  cotangentSumVFormula 45 37 ≤ ((cotangentSumVFormula_45_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_37_unfold]
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
  rw [cotangentSumVFormula_45_37_lower, cotangentSumVFormula_45_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3745_formula_bound :
  (((30702572707115485501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 45) ∧
  (vasyuninBEntryFormula 37 45 ≤ ((30704824506930295749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_37_45_bounds
  have b_Vkh := cotangentSumVFormula_45_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_37_45_lower, cotangentSumVFormula_37_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_37_lower, cotangentSumVFormula_45_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_38_45_unfold :
    cotangentSumVFormula 38 45 =
      ((38/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 38 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_38_45_lower : ℚ := 2413385055055939635073 / 219902325555200000000
def cotangentSumVFormula_38_45_upper : ℚ := 2413385059454113489927 / 219902325555200000000
theorem cotangentSumVFormula_38_45_bounds :
  ((cotangentSumVFormula_38_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 45 ∧
  cotangentSumVFormula 38 45 ≤ ((cotangentSumVFormula_38_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_45_unfold]
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
  rw [cotangentSumVFormula_38_45_lower, cotangentSumVFormula_38_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_38_unfold :
    cotangentSumVFormula 45 38 =
      ((7/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 45 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_45_38_lower : ℚ := -3337362635165358620479 / 439804651110400000000
def cotangentSumVFormula_45_38_upper : ℚ := -3337362626369045285771 / 439804651110400000000
theorem cotangentSumVFormula_45_38_bounds :
  ((cotangentSumVFormula_45_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 38 ∧
  cotangentSumVFormula 45 38 ≤ ((cotangentSumVFormula_45_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_38_unfold]
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
  rw [cotangentSumVFormula_45_38_lower, cotangentSumVFormula_45_38_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3845_formula_bound :
  (((61107311437544017877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 38 45) ∧
  (vasyuninBEntryFormula 38 45 ≤ ((61111815037173763373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 38 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log38 := prim_log_38_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_38_45_bounds
  have b_Vkh := cotangentSumVFormula_45_38_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_38_45_lower, cotangentSumVFormula_38_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_38_lower, cotangentSumVFormula_45_38_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_45_unfold :
    cotangentSumVFormula 41 45 =
      ((41/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 41 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_41_45_lower : ℚ := 1911087735209956731599 / 109951162777600000000
def cotangentSumVFormula_41_45_upper : ℚ := 1911087737409036237151 / 109951162777600000000
theorem cotangentSumVFormula_41_45_bounds :
  ((cotangentSumVFormula_41_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 45 ∧
  cotangentSumVFormula 41 45 ≤ ((cotangentSumVFormula_41_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_45_unfold]
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
  rw [cotangentSumVFormula_41_45_lower, cotangentSumVFormula_41_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_41_unfold :
    cotangentSumVFormula 45 41 =
      ((4/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((8/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((3/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((2/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((6/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((1/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((5/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((9/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 45 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_45_41_lower : ℚ := -3230243266983224427427 / 219902325555200000000
def cotangentSumVFormula_45_41_upper : ℚ := -3230243262585063072573 / 219902325555200000000
theorem cotangentSumVFormula_45_41_bounds :
  ((cotangentSumVFormula_45_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 41 ∧
  cotangentSumVFormula 45 41 ≤ ((cotangentSumVFormula_45_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_41_unfold]
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
  rw [cotangentSumVFormula_45_41_lower, cotangentSumVFormula_45_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4145_formula_bound :
  (((121541416325618145129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 45) ∧
  (vasyuninBEntryFormula 41 45 ≤ ((121550423524877136121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_41_45_bounds
  have b_Vkh := cotangentSumVFormula_45_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_41_45_lower, cotangentSumVFormula_41_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_41_lower, cotangentSumVFormula_45_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_43_45_unfold :
    cotangentSumVFormula 43 45 =
      ((43/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((44/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 43 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_43_45_lower : ℚ := 2988013903393477825349 / 109951162777600000000
def cotangentSumVFormula_43_45_upper : ℚ := 2988013905592576080901 / 109951162777600000000
theorem cotangentSumVFormula_43_45_bounds :
  ((cotangentSumVFormula_43_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 45 ∧
  cotangentSumVFormula 43 45 ≤ ((cotangentSumVFormula_43_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_45_unfold]
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
  rw [cotangentSumVFormula_43_45_lower, cotangentSumVFormula_43_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_43_unfold :
    cotangentSumVFormula 45 43 =
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
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 45 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_45_43_lower : ℚ := -2789896565158104205901 / 109951162777600000000
def cotangentSumVFormula_45_43_upper : ℚ := -2789896562958988762849 / 109951162777600000000
theorem cotangentSumVFormula_45_43_bounds :
  ((cotangentSumVFormula_45_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 43 ∧
  cotangentSumVFormula 45 43 ≤ ((cotangentSumVFormula_45_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_43_unfold]
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
  rw [cotangentSumVFormula_45_43_lower, cotangentSumVFormula_45_43_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4345_formula_bound :
  (((122403273003993707629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 43 45) ∧
  (vasyuninBEntryFormula 43 45 ≤ ((122412280203254261121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 43 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log43 := log_43_certified_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_43_45_bounds
  have b_Vkh := cotangentSumVFormula_45_43_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_43_45_lower, cotangentSumVFormula_43_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_43_lower, cotangentSumVFormula_45_43_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_44_45_unfold :
    cotangentSumVFormula 44 45 =
      ((44/45 : ℚ) : ℝ) * cotangentTermV 1 45    + 
      ((43/45 : ℚ) : ℝ) * cotangentTermV 2 45    + 
      ((42/45 : ℚ) : ℝ) * cotangentTermV 3 45    + 
      ((41/45 : ℚ) : ℝ) * cotangentTermV 4 45    + 
      ((40/45 : ℚ) : ℝ) * cotangentTermV 5 45    + 
      ((39/45 : ℚ) : ℝ) * cotangentTermV 6 45    + 
      ((38/45 : ℚ) : ℝ) * cotangentTermV 7 45    + 
      ((37/45 : ℚ) : ℝ) * cotangentTermV 8 45    + 
      ((36/45 : ℚ) : ℝ) * cotangentTermV 9 45    + 
      ((35/45 : ℚ) : ℝ) * cotangentTermV 10 45    + 
      ((34/45 : ℚ) : ℝ) * cotangentTermV 11 45    + 
      ((33/45 : ℚ) : ℝ) * cotangentTermV 12 45    + 
      ((32/45 : ℚ) : ℝ) * cotangentTermV 13 45    + 
      ((31/45 : ℚ) : ℝ) * cotangentTermV 14 45    + 
      ((30/45 : ℚ) : ℝ) * cotangentTermV 15 45    + 
      ((29/45 : ℚ) : ℝ) * cotangentTermV 16 45    + 
      ((28/45 : ℚ) : ℝ) * cotangentTermV 17 45    + 
      ((27/45 : ℚ) : ℝ) * cotangentTermV 18 45    + 
      ((26/45 : ℚ) : ℝ) * cotangentTermV 19 45    + 
      ((25/45 : ℚ) : ℝ) * cotangentTermV 20 45    + 
      ((24/45 : ℚ) : ℝ) * cotangentTermV 21 45    + 
      ((23/45 : ℚ) : ℝ) * cotangentTermV 22 45    + 
      ((22/45 : ℚ) : ℝ) * cotangentTermV 23 45    + 
      ((21/45 : ℚ) : ℝ) * cotangentTermV 24 45    + 
      ((20/45 : ℚ) : ℝ) * cotangentTermV 25 45    + 
      ((19/45 : ℚ) : ℝ) * cotangentTermV 26 45    + 
      ((18/45 : ℚ) : ℝ) * cotangentTermV 27 45    + 
      ((17/45 : ℚ) : ℝ) * cotangentTermV 28 45    + 
      ((16/45 : ℚ) : ℝ) * cotangentTermV 29 45    + 
      ((15/45 : ℚ) : ℝ) * cotangentTermV 30 45    + 
      ((14/45 : ℚ) : ℝ) * cotangentTermV 31 45    + 
      ((13/45 : ℚ) : ℝ) * cotangentTermV 32 45    + 
      ((12/45 : ℚ) : ℝ) * cotangentTermV 33 45    + 
      ((11/45 : ℚ) : ℝ) * cotangentTermV 34 45    + 
      ((10/45 : ℚ) : ℝ) * cotangentTermV 35 45    + 
      ((9/45 : ℚ) : ℝ) * cotangentTermV 36 45    + 
      ((8/45 : ℚ) : ℝ) * cotangentTermV 37 45    + 
      ((7/45 : ℚ) : ℝ) * cotangentTermV 38 45    + 
      ((6/45 : ℚ) : ℝ) * cotangentTermV 39 45    + 
      ((5/45 : ℚ) : ℝ) * cotangentTermV 40 45    + 
      ((4/45 : ℚ) : ℝ) * cotangentTermV 41 45    + 
      ((3/45 : ℚ) : ℝ) * cotangentTermV 42 45    + 
      ((2/45 : ℚ) : ℝ) * cotangentTermV 43 45    + 
      ((1/45 : ℚ) : ℝ) * cotangentTermV 44 45 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_45]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 44 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_44_45_lower : ℚ := 505624555103022374653 / 13743895347200000000
def cotangentSumVFormula_44_45_upper : ℚ := 252812277688955023611 / 6871947673600000000
theorem cotangentSumVFormula_44_45_bounds :
  ((cotangentSumVFormula_44_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 45 ∧
  cotangentSumVFormula 44 45 ≤ ((cotangentSumVFormula_44_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_45_unfold]
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
  rw [cotangentSumVFormula_44_45_lower, cotangentSumVFormula_44_45_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_45_44_unfold :
    cotangentSumVFormula 45 44 =
      ((1/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 45 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_45_44_lower : ℚ := -980322051446101735069 / 27487790694400000000
def cotangentSumVFormula_45_44_upper : ℚ := -490161025448160655903 / 13743895347200000000
theorem cotangentSumVFormula_45_44_bounds :
  ((cotangentSumVFormula_45_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 44 ∧
  cotangentSumVFormula 45 44 ≤ ((cotangentSumVFormula_45_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_44_unfold]
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
  rw [cotangentSumVFormula_45_44_lower, cotangentSumVFormula_45_44_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4445_formula_bound :
  (((123550755450222676379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 44 45) ∧
  (vasyuninBEntryFormula 44 45 ≤ ((123559762649483417371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 44 45 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log44 := prim_log_44_bounds
  have b_log45 := prim_log_45_bounds
  have b_Vhk := cotangentSumVFormula_44_45_bounds
  have b_Vkh := cotangentSumVFormula_45_44_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [cotangentSumVFormula_44_45_lower, cotangentSumVFormula_44_45_upper] at b_Vhk
  simp only [cotangentSumVFormula_45_44_lower, cotangentSumVFormula_45_44_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_46_unfold :
    cotangentSumVFormula 1 46 =
      ((1/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 1 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_1_46_lower : ℚ := -2084741350160439798263 / 54975581388800000000
def cotangentSumVFormula_1_46_upper : ℚ := -2084741349060875045487 / 54975581388800000000
theorem cotangentSumVFormula_1_46_bounds :
  ((cotangentSumVFormula_1_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 46 ∧
  cotangentSumVFormula 1 46 ≤ ((cotangentSumVFormula_1_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_46_unfold]
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
  rw [cotangentSumVFormula_1_46_lower, cotangentSumVFormula_1_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_1_unfold :
    cotangentSumVFormula 46 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_46_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_46_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_46_1_bounds :
  ((cotangentSumVFormula_46_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 1 ∧
  cotangentSumVFormula 46 1 ≤ ((cotangentSumVFormula_46_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_1_unfold]
  rw [cotangentSumVFormula_46_1_lower, cotangentSumVFormula_46_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_146_formula_bound :
  (((74592955644012579251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 46) ∧
  (vasyuninBEntryFormula 1 46 ≤ ((74595207443867920749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_1_46_bounds
  have b_Vkh := cotangentSumVFormula_46_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_1_46_lower, cotangentSumVFormula_1_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_1_lower, cotangentSumVFormula_46_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_46_unfold :
    cotangentSumVFormula 3 46 =
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
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 3 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_3_46_lower : ℚ := -2449081312152877643401 / 109951162777600000000
def cotangentSumVFormula_3_46_upper : ℚ := -2449081309953749700349 / 109951162777600000000
theorem cotangentSumVFormula_3_46_bounds :
  ((cotangentSumVFormula_3_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 46 ∧
  cotangentSumVFormula 3 46 ≤ ((cotangentSumVFormula_3_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_46_unfold]
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
  rw [cotangentSumVFormula_3_46_lower, cotangentSumVFormula_3_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_3_unfold :
    cotangentSumVFormula 46 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_46_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_46_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_46_3_bounds :
  ((cotangentSumVFormula_46_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 3 ∧
  cotangentSumVFormula 46 3 ≤ ((cotangentSumVFormula_46_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_46_3_lower, cotangentSumVFormula_46_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_346_formula_bound :
  (((61035798334313673001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 46) ∧
  (vasyuninBEntryFormula 3 46 ≤ ((61038050134140951999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_3_46_bounds
  have b_Vkh := cotangentSumVFormula_46_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_3_46_lower, cotangentSumVFormula_3_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_3_lower, cotangentSumVFormula_46_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_46_unfold :
    cotangentSumVFormula 5 46 =
      ((5/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 5 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_5_46_lower : ℚ := -202505918767876844097 / 13743895347200000000
def cotangentSumVFormula_5_46_upper : ℚ := -1620047347943887981599 / 109951162777600000000
theorem cotangentSumVFormula_5_46_bounds :
  ((cotangentSumVFormula_5_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 46 ∧
  cotangentSumVFormula 5 46 ≤ ((cotangentSumVFormula_5_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_46_unfold]
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
  rw [cotangentSumVFormula_5_46_lower, cotangentSumVFormula_5_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_5_unfold :
    cotangentSumVFormula 46 5 =
      ((1/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_46_5_lower : ℚ := -3134269962581291229457 / 3518437208883200000000
def cotangentSumVFormula_46_5_upper : ℚ := -3134269892212532208043 / 3518437208883200000000
theorem cotangentSumVFormula_46_5_bounds :
  ((cotangentSumVFormula_46_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 5 ∧
  cotangentSumVFormula 46 5 ≤ ((cotangentSumVFormula_46_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_46_5_lower, cotangentSumVFormula_46_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_546_formula_bound :
  (((54810510346341235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 46) ∧
  (vasyuninBEntryFormula 5 46 ≤ ((54812762146162826999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_5_46_bounds
  have b_Vkh := cotangentSumVFormula_46_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_5_46_lower, cotangentSumVFormula_5_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_5_lower, cotangentSumVFormula_46_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_46_unfold :
    cotangentSumVFormula 7 46 =
      ((7/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 7 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_7_46_lower : ℚ := -2449037223127354114927 / 219902325555200000000
def cotangentSumVFormula_7_46_upper : ℚ := -2449037218729099010073 / 219902325555200000000
theorem cotangentSumVFormula_7_46_bounds :
  ((cotangentSumVFormula_7_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 46 ∧
  cotangentSumVFormula 7 46 ≤ ((cotangentSumVFormula_7_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_46_unfold]
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
  rw [cotangentSumVFormula_7_46_lower, cotangentSumVFormula_7_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_7_unfold :
    cotangentSumVFormula 46 7 =
      ((4/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_46_7_lower : ℚ := -2465148184743653589703 / 14073748835532800000000
def cotangentSumVFormula_46_7_upper : ℚ := -2465147903268565160297 / 14073748835532800000000
theorem cotangentSumVFormula_46_7_bounds :
  ((cotangentSumVFormula_46_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 7 ∧
  cotangentSumVFormula 46 7 ≤ ((cotangentSumVFormula_46_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_7_unfold]
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
  rw [cotangentSumVFormula_46_7_lower, cotangentSumVFormula_46_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_746_formula_bound :
  (((6321358515170722797 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 46) ∧
  (vasyuninBEntryFormula 7 46 ≤ ((25286559960592561937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_7_46_bounds
  have b_Vkh := cotangentSumVFormula_46_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_7_46_lower, cotangentSumVFormula_7_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_7_lower, cotangentSumVFormula_46_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_46_unfold :
    cotangentSumVFormula 9 46 =
      ((9/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 9 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_9_46_lower : ℚ := -2337692276678524245479 / 439804651110400000000
def cotangentSumVFormula_9_46_upper : ℚ := -2337692267882019504521 / 439804651110400000000
theorem cotangentSumVFormula_9_46_bounds :
  ((cotangentSumVFormula_9_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 46 ∧
  cotangentSumVFormula 9 46 ≤ ((cotangentSumVFormula_9_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_46_unfold]
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
  rw [cotangentSumVFormula_9_46_lower, cotangentSumVFormula_9_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_9_unfold :
    cotangentSumVFormula 46 9 =
      ((1/9 : ℚ) : ℝ) * cotangentTermV 1 9    + 
      ((2/9 : ℚ) : ℝ) * cotangentTermV 2 9    + 
      ((3/9 : ℚ) : ℝ) * cotangentTermV 3 9    + 
      ((4/9 : ℚ) : ℝ) * cotangentTermV 4 9    + 
      ((5/9 : ℚ) : ℝ) * cotangentTermV 5 9    + 
      ((6/9 : ℚ) : ℝ) * cotangentTermV 6 9    + 
      ((7/9 : ℚ) : ℝ) * cotangentTermV 7 9    + 
      ((8/9 : ℚ) : ℝ) * cotangentTermV 8 9 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_9]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_46_9_lower : ℚ := -1324275640802612526729 / 439804651110400000000
def cotangentSumVFormula_46_9_upper : ℚ := -82767227000406858681 / 27487790694400000000
theorem cotangentSumVFormula_46_9_bounds :
  ((cotangentSumVFormula_46_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 9 ∧
  cotangentSumVFormula 46 9 ≤ ((cotangentSumVFormula_46_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_9_unfold]
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
  rw [cotangentSumVFormula_46_9_lower, cotangentSumVFormula_46_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_946_formula_bound :
  (((95541391273020517877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 46) ∧
  (vasyuninBEntryFormula 9 46 ≤ ((95545894872656700873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_9_46_bounds
  have b_Vkh := cotangentSumVFormula_46_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_9_46_lower, cotangentSumVFormula_9_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_9_lower, cotangentSumVFormula_46_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_46_unfold :
    cotangentSumVFormula 11 46 =
      ((11/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 11 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_11_46_lower : ℚ := -6539118809804478559 / 1717986918400000000
def cotangentSumVFormula_11_46_upper : ℚ := -104625900407091233681 / 27487790694400000000
theorem cotangentSumVFormula_11_46_bounds :
  ((cotangentSumVFormula_11_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 46 ∧
  cotangentSumVFormula 11 46 ≤ ((cotangentSumVFormula_11_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_46_unfold]
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
  rw [cotangentSumVFormula_11_46_lower, cotangentSumVFormula_11_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_11_unfold :
    cotangentSumVFormula 46 11 =
      ((2/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_46_11_lower : ℚ := -1924262803088862162833 / 879609302220800000000
def cotangentSumVFormula_46_11_upper : ℚ := -1924262785496647212167 / 879609302220800000000
theorem cotangentSumVFormula_46_11_bounds :
  ((cotangentSumVFormula_46_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 11 ∧
  cotangentSumVFormula 46 11 ≤ ((cotangentSumVFormula_46_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_11_unfold]
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
  rw [cotangentSumVFormula_46_11_lower, cotangentSumVFormula_46_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1146_formula_bound :
  (((90363415568724611627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 46) ∧
  (vasyuninBEntryFormula 11 46 ≤ ((90367919168358888373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_11_46_bounds
  have b_Vkh := cotangentSumVFormula_46_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_11_46_lower, cotangentSumVFormula_11_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_11_lower, cotangentSumVFormula_46_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_46_unfold :
    cotangentSumVFormula 13 46 =
      ((13/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 13 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_13_46_lower : ℚ := -1173495296890450807979 / 439804651110400000000
def cotangentSumVFormula_13_46_upper : ℚ := -1173495288093971067021 / 439804651110400000000
theorem cotangentSumVFormula_13_46_bounds :
  ((cotangentSumVFormula_13_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 46 ∧
  cotangentSumVFormula 13 46 ≤ ((cotangentSumVFormula_13_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_46_unfold]
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
  rw [cotangentSumVFormula_13_46_lower, cotangentSumVFormula_13_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_13_unfold :
    cotangentSumVFormula 46 13 =
      ((7/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_46_13_lower : ℚ := -632007574020206276729 / 439804651110400000000
def cotangentSumVFormula_46_13_upper : ℚ := -1264015130448186274667 / 879609302220800000000
theorem cotangentSumVFormula_46_13_bounds :
  ((cotangentSumVFormula_46_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 13 ∧
  cotangentSumVFormula 46 13 ≤ ((cotangentSumVFormula_46_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_13_unfold]
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
  rw [cotangentSumVFormula_46_13_lower, cotangentSumVFormula_46_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1346_formula_bound :
  (((42901847001192704251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 46) ∧
  (vasyuninBEntryFormula 13 46 ≤ ((21452049400504655687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_13_46_bounds
  have b_Vkh := cotangentSumVFormula_46_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_13_46_lower, cotangentSumVFormula_13_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_13_lower, cotangentSumVFormula_46_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_46_unfold :
    cotangentSumVFormula 15 46 =
      ((15/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 15 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_15_46_lower : ℚ := 1905458214795787473271 / 439804651110400000000
def cotangentSumVFormula_15_46_upper : ℚ := 1905458223592251589229 / 439804651110400000000
theorem cotangentSumVFormula_15_46_bounds :
  ((cotangentSumVFormula_15_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 46 ∧
  cotangentSumVFormula 15 46 ≤ ((cotangentSumVFormula_15_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_46_unfold]
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
  rw [cotangentSumVFormula_15_46_lower, cotangentSumVFormula_15_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_15_unfold :
    cotangentSumVFormula 46 15 =
      ((1/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((4/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_46_15_lower : ℚ := -1590970988452579896177 / 219902325555200000000
def cotangentSumVFormula_46_15_upper : ℚ := -397742746013629732987 / 54975581388800000000
theorem cotangentSumVFormula_46_15_bounds :
  ((cotangentSumVFormula_46_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 15 ∧
  cotangentSumVFormula 46 15 ≤ ((cotangentSumVFormula_46_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_15_unfold]
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
  rw [cotangentSumVFormula_46_15_lower, cotangentSumVFormula_46_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1546_formula_bound :
  (((10459193905773398719 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 46) ∧
  (vasyuninBEntryFormula 15 46 ≤ ((41839027422909764499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_15_46_bounds
  have b_Vkh := cotangentSumVFormula_46_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_15_46_lower, cotangentSumVFormula_15_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_15_lower, cotangentSumVFormula_46_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_46_unfold :
    cotangentSumVFormula 17 46 =
      ((17/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 17 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_17_46_lower : ℚ := -2360771267802891850333 / 879609302220800000000
def cotangentSumVFormula_17_46_upper : ℚ := -2360771250209973774667 / 879609302220800000000
theorem cotangentSumVFormula_17_46_bounds :
  ((cotangentSumVFormula_17_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 46 ∧
  cotangentSumVFormula 17 46 ≤ ((cotangentSumVFormula_17_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_46_unfold]
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
  rw [cotangentSumVFormula_17_46_lower, cotangentSumVFormula_17_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_17_unfold :
    cotangentSumVFormula 46 17 =
      ((12/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_46_17_lower : ℚ := 140856414383029387849 / 109951162777600000000
def cotangentSumVFormula_46_17_upper : ℚ := 1126851332656487944083 / 879609302220800000000
theorem cotangentSumVFormula_46_17_bounds :
  ((cotangentSumVFormula_46_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 17 ∧
  cotangentSumVFormula 46 17 ≤ ((cotangentSumVFormula_46_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_17_unfold]
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
  rw [cotangentSumVFormula_46_17_lower, cotangentSumVFormula_46_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1746_formula_bound :
  (((39564677942391360501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 46) ∧
  (vasyuninBEntryFormula 17 46 ≤ ((39566929742207233249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_17_46_bounds
  have b_Vkh := cotangentSumVFormula_46_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_17_46_lower, cotangentSumVFormula_17_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_17_lower, cotangentSumVFormula_46_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
