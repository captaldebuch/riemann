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

theorem cotangentSumVFormula_34_39_unfold :
    cotangentSumVFormula 34 39 =
      ((34/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 34 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_34_39_lower : ℚ := 677786383378573482987 / 54975581388800000000
def cotangentSumVFormula_34_39_upper : ℚ := 677786384478107767013 / 54975581388800000000
theorem cotangentSumVFormula_34_39_bounds :
  ((cotangentSumVFormula_34_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 34 39 ∧
  cotangentSumVFormula 34 39 ≤ ((cotangentSumVFormula_34_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_34_39_unfold]
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
  rw [cotangentSumVFormula_34_39_lower, cotangentSumVFormula_34_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_34_unfold :
    cotangentSumVFormula 39 34 =
      ((5/34 : ℚ) : ℝ) * cotangentTermV 1 34    + 
      ((10/34 : ℚ) : ℝ) * cotangentTermV 2 34    + 
      ((15/34 : ℚ) : ℝ) * cotangentTermV 3 34    + 
      ((20/34 : ℚ) : ℝ) * cotangentTermV 4 34    + 
      ((25/34 : ℚ) : ℝ) * cotangentTermV 5 34    + 
      ((30/34 : ℚ) : ℝ) * cotangentTermV 6 34    + 
      ((1/34 : ℚ) : ℝ) * cotangentTermV 7 34    + 
      ((6/34 : ℚ) : ℝ) * cotangentTermV 8 34    + 
      ((11/34 : ℚ) : ℝ) * cotangentTermV 9 34    + 
      ((16/34 : ℚ) : ℝ) * cotangentTermV 10 34    + 
      ((21/34 : ℚ) : ℝ) * cotangentTermV 11 34    + 
      ((26/34 : ℚ) : ℝ) * cotangentTermV 12 34    + 
      ((31/34 : ℚ) : ℝ) * cotangentTermV 13 34    + 
      ((2/34 : ℚ) : ℝ) * cotangentTermV 14 34    + 
      ((7/34 : ℚ) : ℝ) * cotangentTermV 15 34    + 
      ((12/34 : ℚ) : ℝ) * cotangentTermV 16 34    + 
      ((17/34 : ℚ) : ℝ) * cotangentTermV 17 34    + 
      ((22/34 : ℚ) : ℝ) * cotangentTermV 18 34    + 
      ((27/34 : ℚ) : ℝ) * cotangentTermV 19 34    + 
      ((32/34 : ℚ) : ℝ) * cotangentTermV 20 34    + 
      ((3/34 : ℚ) : ℝ) * cotangentTermV 21 34    + 
      ((8/34 : ℚ) : ℝ) * cotangentTermV 22 34    + 
      ((13/34 : ℚ) : ℝ) * cotangentTermV 23 34    + 
      ((18/34 : ℚ) : ℝ) * cotangentTermV 24 34    + 
      ((23/34 : ℚ) : ℝ) * cotangentTermV 25 34    + 
      ((28/34 : ℚ) : ℝ) * cotangentTermV 26 34    + 
      ((33/34 : ℚ) : ℝ) * cotangentTermV 27 34    + 
      ((4/34 : ℚ) : ℝ) * cotangentTermV 28 34    + 
      ((9/34 : ℚ) : ℝ) * cotangentTermV 29 34    + 
      ((14/34 : ℚ) : ℝ) * cotangentTermV 30 34    + 
      ((19/34 : ℚ) : ℝ) * cotangentTermV 31 34    + 
      ((24/34 : ℚ) : ℝ) * cotangentTermV 32 34    + 
      ((29/34 : ℚ) : ℝ) * cotangentTermV 33 34 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_34]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((5/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((10/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((15/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((20/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((25/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((30/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((1/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((6/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((11/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((16/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((21/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((26/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((31/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((2/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((7/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((12/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((17/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((22/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((27/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((32/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((3/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((8/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((13/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((18/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((23/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((28/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((33/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((4/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((9/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((14/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((19/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((24/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((29/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33]
  try ring

def cotangentSumVFormula_39_34_lower : ℚ := -526692793386877298263 / 54975581388800000000
def cotangentSumVFormula_39_34_upper : ℚ := -1053385584574684856599 / 109951162777600000000
theorem cotangentSumVFormula_39_34_bounds :
  ((cotangentSumVFormula_39_34_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 34 ∧
  cotangentSumVFormula 39 34 ≤ ((cotangentSumVFormula_39_34_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_34_unfold]
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
  rw [cotangentSumVFormula_39_34_lower, cotangentSumVFormula_39_34_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3439_formula_bound :
  (((140449382896650926379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 34 39) ∧
  (vasyuninBEntryFormula 34 39 ≤ ((140458390095910479871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 34 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log34 := prim_log_34_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_34_39_bounds
  have b_Vkh := cotangentSumVFormula_39_34_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_34_lower, prim_log_34_upper] at b_log34
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_34_39_lower, cotangentSumVFormula_34_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_34_lower, cotangentSumVFormula_39_34_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_35_39_unfold :
    cotangentSumVFormula 35 39 =
      ((35/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 35 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_35_39_lower : ℚ := 3164085501095095103823 / 219902325555200000000
def cotangentSumVFormula_35_39_upper : ℚ := 3164085505493230677427 / 219902325555200000000
theorem cotangentSumVFormula_35_39_bounds :
  ((cotangentSumVFormula_35_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 39 ∧
  cotangentSumVFormula 35 39 ≤ ((cotangentSumVFormula_35_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_39_unfold]
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
  rw [cotangentSumVFormula_35_39_lower, cotangentSumVFormula_35_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_35_unfold :
    cotangentSumVFormula 39 35 =
      ((4/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_39_35_lower : ℚ := -1307100911898076080901 / 109951162777600000000
def cotangentSumVFormula_39_35_upper : ℚ := -326775227424750608681 / 27487790694400000000
theorem cotangentSumVFormula_39_35_bounds :
  ((cotangentSumVFormula_39_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 35 ∧
  cotangentSumVFormula 39 35 ≤ ((cotangentSumVFormula_39_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_35_unfold]
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
  rw [cotangentSumVFormula_39_35_lower, cotangentSumVFormula_39_35_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3539_formula_bound :
  (((17527240793075250563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 35 39) ∧
  (vasyuninBEntryFormula 35 39 ≤ ((8764183346491351281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 35 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log35 := prim_log_35_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_35_39_bounds
  have b_Vkh := cotangentSumVFormula_39_35_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_35_39_lower, cotangentSumVFormula_35_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_35_lower, cotangentSumVFormula_39_35_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_39_unfold :
    cotangentSumVFormula 37 39 =
      ((37/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_37_39_lower : ℚ := 2403589918296705169099 / 109951162777600000000
def cotangentSumVFormula_37_39_upper : ℚ := 2403589920495770612151 / 109951162777600000000
theorem cotangentSumVFormula_37_39_bounds :
  ((cotangentSumVFormula_37_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 39 ∧
  cotangentSumVFormula 37 39 ≤ ((cotangentSumVFormula_37_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_39_unfold]
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
  rw [cotangentSumVFormula_37_39_lower, cotangentSumVFormula_37_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_37_unfold :
    cotangentSumVFormula 39 37 =
      ((2/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_39_37_lower : ℚ := -2215734768764665143401 / 109951162777600000000
def cotangentSumVFormula_39_37_upper : ℚ := -2215734766565595794099 / 109951162777600000000
theorem cotangentSumVFormula_39_37_bounds :
  ((cotangentSumVFormula_39_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 37 ∧
  cotangentSumVFormula 39 37 ≤ ((cotangentSumVFormula_39_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_37_unfold]
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
  rw [cotangentSumVFormula_39_37_lower, cotangentSumVFormula_39_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3739_formula_bound :
  (((2202609462778900461 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 39) ∧
  (vasyuninBEntryFormula 37 39 ≤ ((17622001602138593187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_37_39_bounds
  have b_Vkh := cotangentSumVFormula_39_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_37_39_lower, cotangentSumVFormula_37_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_37_lower, cotangentSumVFormula_39_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_38_39_unfold :
    cotangentSumVFormula 38 39 =
      ((38/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 38 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_38_39_lower : ℚ := 12949479561431204579 / 429496729600000000
def cotangentSumVFormula_38_39_upper : ℚ := 207191673120341742361 / 6871947673600000000
theorem cotangentSumVFormula_38_39_bounds :
  ((cotangentSumVFormula_38_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 39 ∧
  cotangentSumVFormula 38 39 ≤ ((cotangentSumVFormula_38_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_39_unfold]
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
  rw [cotangentSumVFormula_38_39_lower, cotangentSumVFormula_38_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_38_unfold :
    cotangentSumVFormula 39 38 =
      ((1/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_39_38_lower : ℚ := -399553660022559656597 / 13743895347200000000
def cotangentSumVFormula_39_38_upper : ℚ := -1598214638990698482987 / 54975581388800000000
theorem cotangentSumVFormula_39_38_bounds :
  ((cotangentSumVFormula_39_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 38 ∧
  cotangentSumVFormula 39 38 ≤ ((cotangentSumVFormula_39_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_38_unfold]
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
  rw [cotangentSumVFormula_39_38_lower, cotangentSumVFormula_39_38_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3839_formula_bound :
  (((8893641068715648719 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 38 39) ∧
  (vasyuninBEntryFormula 38 39 ≤ ((35576816074677608249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 38 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log38 := prim_log_38_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_38_39_bounds
  have b_Vkh := cotangentSumVFormula_39_38_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_38_39_lower, cotangentSumVFormula_38_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_38_lower, cotangentSumVFormula_39_38_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_40_unfold :
    cotangentSumVFormula 1 40 =
      ((1/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_1_40_lower : ℚ := -3434602080181775299651 / 109951162777600000000
def cotangentSumVFormula_1_40_upper : ℚ := -3434602077982687981599 / 109951162777600000000
theorem cotangentSumVFormula_1_40_bounds :
  ((cotangentSumVFormula_1_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 40 ∧
  cotangentSumVFormula 1 40 ≤ ((cotangentSumVFormula_1_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_40_unfold]
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
  rw [cotangentSumVFormula_1_40_lower, cotangentSumVFormula_1_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_1_unfold :
    cotangentSumVFormula 40 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_40_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_40_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_40_1_bounds :
  ((cotangentSumVFormula_40_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 1 ∧
  cotangentSumVFormula 40 1 ≤ ((cotangentSumVFormula_40_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_1_unfold]
  rw [cotangentSumVFormula_40_1_lower, cotangentSumVFormula_40_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_140_formula_bound :
  (((83827673776968548001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 40) ∧
  (vasyuninBEntryFormula 1 40 ≤ ((83829925576811451999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_1_40_bounds
  have b_Vkh := cotangentSumVFormula_40_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_1_40_lower, cotangentSumVFormula_1_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_1_lower, cotangentSumVFormula_40_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_40_unfold :
    cotangentSumVFormula 3 40 =
      ((3/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 3 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_3_40_lower : ℚ := -1944819489503094830901 / 109951162777600000000
def cotangentSumVFormula_3_40_upper : ℚ := -1944819487304005950349 / 109951162777600000000
theorem cotangentSumVFormula_3_40_bounds :
  ((cotangentSumVFormula_3_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 40 ∧
  cotangentSumVFormula 3 40 ≤ ((cotangentSumVFormula_3_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_40_unfold]
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
  rw [cotangentSumVFormula_3_40_lower, cotangentSumVFormula_3_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_3_unfold :
    cotangentSumVFormula 40 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_40_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_40_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_40_3_bounds :
  ((cotangentSumVFormula_40_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 3 ∧
  cotangentSumVFormula 40 3 ≤ ((cotangentSumVFormula_40_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_40_3_lower, cotangentSumVFormula_40_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_340_formula_bound :
  (((136435618872378174127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 40) ∧
  (vasyuninBEntryFormula 3 40 ≤ ((136440122472025575873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_3_40_bounds
  have b_Vkh := cotangentSumVFormula_40_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_3_40_lower, cotangentSumVFormula_3_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_3_lower, cotangentSumVFormula_40_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_40_unfold :
    cotangentSumVFormula 7 40 =
      ((7/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_7_40_lower : ℚ := -1970432548507843958677 / 219902325555200000000
def cotangentSumVFormula_7_40_upper : ℚ := -1970432544109676353823 / 219902325555200000000
theorem cotangentSumVFormula_7_40_bounds :
  ((cotangentSumVFormula_7_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 40 ∧
  cotangentSumVFormula 7 40 ≤ ((cotangentSumVFormula_7_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_40_unfold]
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
  rw [cotangentSumVFormula_7_40_lower, cotangentSumVFormula_7_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_7_unfold :
    cotangentSumVFormula 40 7 =
      ((5/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_40_7_lower : ℚ := 2156738354928926739293 / 3518437208883200000000
def cotangentSumVFormula_40_7_upper : ℚ := 2156738425297699041957 / 3518437208883200000000
theorem cotangentSumVFormula_40_7_bounds :
  ((cotangentSumVFormula_40_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 7 ∧
  cotangentSumVFormula 40 7 ≤ ((cotangentSumVFormula_40_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_7_unfold]
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
  rw [cotangentSumVFormula_40_7_lower, cotangentSumVFormula_40_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_740_formula_bound :
  (((56208558915164173001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 40) ∧
  (vasyuninBEntryFormula 7 40 ≤ ((56210810714981764499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_7_40_bounds
  have b_Vkh := cotangentSumVFormula_40_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_7_40_lower, cotangentSumVFormula_7_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_7_lower, cotangentSumVFormula_40_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_40_unfold :
    cotangentSumVFormula 9 40 =
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
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 9 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_9_40_lower : ℚ := -691514057291828424651 / 109951162777600000000
def cotangentSumVFormula_9_40_upper : ℚ := -1383028110185484166323 / 219902325555200000000
theorem cotangentSumVFormula_9_40_bounds :
  ((cotangentSumVFormula_9_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 40 ∧
  cotangentSumVFormula 9 40 ≤ ((cotangentSumVFormula_9_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_40_unfold]
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
  rw [cotangentSumVFormula_9_40_lower, cotangentSumVFormula_9_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_9_unfold :
    cotangentSumVFormula 40 9 =
      ((4/9 : ℚ) : ℝ) * cotangentTermV 1 9    + 
      ((8/9 : ℚ) : ℝ) * cotangentTermV 2 9    + 
      ((3/9 : ℚ) : ℝ) * cotangentTermV 3 9    + 
      ((7/9 : ℚ) : ℝ) * cotangentTermV 4 9    + 
      ((2/9 : ℚ) : ℝ) * cotangentTermV 5 9    + 
      ((6/9 : ℚ) : ℝ) * cotangentTermV 6 9    + 
      ((1/9 : ℚ) : ℝ) * cotangentTermV 7 9    + 
      ((5/9 : ℚ) : ℝ) * cotangentTermV 8 9 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_9]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_40_9_lower : ℚ := 927378290468754971209 / 1759218604441600000000
def cotangentSumVFormula_40_9_upper : ℚ := 927378325653165341291 / 1759218604441600000000
theorem cotangentSumVFormula_40_9_bounds :
  ((cotangentSumVFormula_40_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 9 ∧
  cotangentSumVFormula 40 9 ≤ ((cotangentSumVFormula_40_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_9_unfold]
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
  rw [cotangentSumVFormula_40_9_lower, cotangentSumVFormula_40_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_940_formula_bound :
  (((13148264309807367469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 40) ∧
  (vasyuninBEntryFormula 9 40 ≤ ((13148827259761601281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_9_40_bounds
  have b_Vkh := cotangentSumVFormula_40_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_9_40_lower, cotangentSumVFormula_9_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_9_lower, cotangentSumVFormula_40_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_40_unfold :
    cotangentSumVFormula 11 40 =
      ((11/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_11_40_lower : ℚ := -1033309839549059583677 / 219902325555200000000
def cotangentSumVFormula_11_40_upper : ℚ := -129163729393861546181 / 27487790694400000000
theorem cotangentSumVFormula_11_40_bounds :
  ((cotangentSumVFormula_11_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 40 ∧
  cotangentSumVFormula 11 40 ≤ ((cotangentSumVFormula_11_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_40_unfold]
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
  rw [cotangentSumVFormula_11_40_lower, cotangentSumVFormula_11_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_11_unfold :
    cotangentSumVFormula 40 11 =
      ((7/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_40_11_lower : ℚ := 774511245798822212167 / 879609302220800000000
def cotangentSumVFormula_40_11_upper : ℚ := 774511263391034037833 / 879609302220800000000
theorem cotangentSumVFormula_40_11_bounds :
  ((cotangentSumVFormula_40_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 11 ∧
  cotangentSumVFormula 40 11 ≤ ((cotangentSumVFormula_40_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_11_unfold]
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
  rw [cotangentSumVFormula_40_11_lower, cotangentSumVFormula_40_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1140_formula_bound :
  (((24853132059037844313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 40) ∧
  (vasyuninBEntryFormula 11 40 ≤ ((49708515917891920749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_11_40_bounds
  have b_Vkh := cotangentSumVFormula_40_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_11_40_lower, cotangentSumVFormula_11_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_11_lower, cotangentSumVFormula_40_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_40_unfold :
    cotangentSumVFormula 13 40 =
      ((13/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_13_40_lower : ℚ := 1402830286465883567021 / 439804651110400000000
def cotangentSumVFormula_13_40_upper : ℚ := 1402830295262221120479 / 439804651110400000000
theorem cotangentSumVFormula_13_40_bounds :
  ((cotangentSumVFormula_13_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 40 ∧
  cotangentSumVFormula 13 40 ≤ ((cotangentSumVFormula_13_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_40_unfold]
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
  rw [cotangentSumVFormula_13_40_lower, cotangentSumVFormula_13_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_13_unfold :
    cotangentSumVFormula 40 13 =
      ((1/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_40_13_lower : ℚ := -2516650550571192214229 / 439804651110400000000
def cotangentSumVFormula_40_13_upper : ℚ := -2516650541775076535771 / 439804651110400000000
theorem cotangentSumVFormula_40_13_bounds :
  ((cotangentSumVFormula_40_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 13 ∧
  cotangentSumVFormula 40 13 ≤ ((cotangentSumVFormula_40_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_13_unfold]
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
  rw [cotangentSumVFormula_40_13_lower, cotangentSumVFormula_40_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1340_formula_bound :
  (((48093347205741298001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 40) ∧
  (vasyuninBEntryFormula 13 40 ≤ ((48095599005557233249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_13_40_bounds
  have b_Vkh := cotangentSumVFormula_40_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_13_40_lower, cotangentSumVFormula_13_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_13_lower, cotangentSumVFormula_40_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_40_unfold :
    cotangentSumVFormula 17 40 =
      ((17/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_17_40_lower : ℚ := 1705475202638661274667 / 879609302220800000000
def cotangentSumVFormula_17_40_upper : ℚ := 1705475220231301225333 / 879609302220800000000
theorem cotangentSumVFormula_17_40_bounds :
  ((cotangentSumVFormula_17_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 40 ∧
  cotangentSumVFormula 17 40 ≤ ((cotangentSumVFormula_17_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_40_unfold]
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
  rw [cotangentSumVFormula_17_40_lower, cotangentSumVFormula_17_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_17_unfold :
    cotangentSumVFormula 40 17 =
      ((6/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_40_17_lower : ℚ := -909029662072531276729 / 439804651110400000000
def cotangentSumVFormula_40_17_upper : ℚ := -909029653276402317021 / 439804651110400000000
theorem cotangentSumVFormula_40_17_bounds :
  ((cotangentSumVFormula_40_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 17 ∧
  cotangentSumVFormula 40 17 ≤ ((cotangentSumVFormula_40_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_17_unfold]
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
  rw [cotangentSumVFormula_40_17_lower, cotangentSumVFormula_40_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1740_formula_bound :
  (((87055445404123111627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 40) ∧
  (vasyuninBEntryFormula 17 40 ≤ ((87059949003753888373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_17_40_bounds
  have b_Vkh := cotangentSumVFormula_40_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_17_40_lower, cotangentSumVFormula_17_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_17_lower, cotangentSumVFormula_40_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_40_unfold :
    cotangentSumVFormula 19 40 =
      ((19/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_19_40_lower : ℚ := 3056303280900189035771 / 439804651110400000000
def cotangentSumVFormula_19_40_upper : ℚ := 3056303289696512526729 / 439804651110400000000
theorem cotangentSumVFormula_19_40_bounds :
  ((cotangentSumVFormula_19_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 40 ∧
  cotangentSumVFormula 19 40 ≤ ((cotangentSumVFormula_19_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_40_unfold]
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
  rw [cotangentSumVFormula_19_40_lower, cotangentSumVFormula_19_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_19_unfold :
    cotangentSumVFormula 40 19 =
      ((2/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_40_19_lower : ℚ := -1456974933957273646177 / 219902325555200000000
def cotangentSumVFormula_40_19_upper : ℚ := -728487464779602044099 / 109951162777600000000
theorem cotangentSumVFormula_40_19_bounds :
  ((cotangentSumVFormula_40_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 19 ∧
  cotangentSumVFormula 40 19 ≤ ((cotangentSumVFormula_40_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_19_unfold]
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
  rw [cotangentSumVFormula_40_19_lower, cotangentSumVFormula_40_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1940_formula_bound :
  (((85520098041282986627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 40) ∧
  (vasyuninBEntryFormula 19 40 ≤ ((85524601640913575873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_19_40_bounds
  have b_Vkh := cotangentSumVFormula_40_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_19_40_lower, cotangentSumVFormula_19_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_19_lower, cotangentSumVFormula_40_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_21_40_unfold :
    cotangentSumVFormula 21 40 =
      ((21/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 21 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_21_40_lower : ℚ := -1528151644848239271177 / 219902325555200000000
def cotangentSumVFormula_21_40_upper : ℚ := -382037910112521139237 / 54975581388800000000
theorem cotangentSumVFormula_21_40_bounds :
  ((cotangentSumVFormula_21_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 21 40 ∧
  cotangentSumVFormula 21 40 ≤ ((cotangentSumVFormula_21_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_21_40_unfold]
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
  rw [cotangentSumVFormula_21_40_lower, cotangentSumVFormula_21_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_21_unfold :
    cotangentSumVFormula 40 21 =
      ((19/21 : ℚ) : ℝ) * cotangentTermV 1 21    + 
      ((17/21 : ℚ) : ℝ) * cotangentTermV 2 21    + 
      ((15/21 : ℚ) : ℝ) * cotangentTermV 3 21    + 
      ((13/21 : ℚ) : ℝ) * cotangentTermV 4 21    + 
      ((11/21 : ℚ) : ℝ) * cotangentTermV 5 21    + 
      ((9/21 : ℚ) : ℝ) * cotangentTermV 6 21    + 
      ((7/21 : ℚ) : ℝ) * cotangentTermV 7 21    + 
      ((5/21 : ℚ) : ℝ) * cotangentTermV 8 21    + 
      ((3/21 : ℚ) : ℝ) * cotangentTermV 9 21    + 
      ((1/21 : ℚ) : ℝ) * cotangentTermV 10 21    + 
      ((20/21 : ℚ) : ℝ) * cotangentTermV 11 21    + 
      ((18/21 : ℚ) : ℝ) * cotangentTermV 12 21    + 
      ((16/21 : ℚ) : ℝ) * cotangentTermV 13 21    + 
      ((14/21 : ℚ) : ℝ) * cotangentTermV 14 21    + 
      ((12/21 : ℚ) : ℝ) * cotangentTermV 15 21    + 
      ((10/21 : ℚ) : ℝ) * cotangentTermV 16 21    + 
      ((8/21 : ℚ) : ℝ) * cotangentTermV 17 21    + 
      ((6/21 : ℚ) : ℝ) * cotangentTermV 18 21    + 
      ((4/21 : ℚ) : ℝ) * cotangentTermV 19 21    + 
      ((2/21 : ℚ) : ℝ) * cotangentTermV 20 21 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_21]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((19/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((17/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((15/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((13/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((11/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((9/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((7/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((5/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((3/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((1/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((20/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((18/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((16/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((14/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((12/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((10/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((8/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((6/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((4/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((2/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20]
  try ring

def cotangentSumVFormula_40_21_lower : ℚ := 3485642971864243723271 / 439804651110400000000
def cotangentSumVFormula_40_21_upper : ℚ := 3485642980660386745479 / 439804651110400000000
theorem cotangentSumVFormula_40_21_bounds :
  ((cotangentSumVFormula_40_21_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 21 ∧
  cotangentSumVFormula 40 21 ≤ ((cotangentSumVFormula_40_21_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_21_unfold]
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
  rw [cotangentSumVFormula_40_21_lower, cotangentSumVFormula_40_21_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2140_formula_bound :
  (((2579728312916900461 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 21 40) ∧
  (vasyuninBEntryFormula 21 40 ≤ ((20638952403242749437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 21 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log21 := prim_log_21_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_21_40_bounds
  have b_Vkh := cotangentSumVFormula_40_21_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_21_lower, prim_log_21_upper] at b_log21
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_21_40_lower, cotangentSumVFormula_21_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_21_lower, cotangentSumVFormula_40_21_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_40_unfold :
    cotangentSumVFormula 23 40 =
      ((23/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 23 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_23_40_lower : ℚ := -3410950440462491903791 / 1759218604441600000000
def cotangentSumVFormula_23_40_upper : ℚ := -3410950405277217471209 / 1759218604441600000000
theorem cotangentSumVFormula_23_40_bounds :
  ((cotangentSumVFormula_23_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 40 ∧
  cotangentSumVFormula 23 40 ≤ ((cotangentSumVFormula_23_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_40_unfold]
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
  rw [cotangentSumVFormula_23_40_lower, cotangentSumVFormula_23_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_23_unfold :
    cotangentSumVFormula 40 23 =
      ((17/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_40_23_lower : ℚ := 3398711381711899555917 / 879609302220800000000
def cotangentSumVFormula_40_23_upper : ℚ := 3398711399304231694083 / 879609302220800000000
theorem cotangentSumVFormula_40_23_bounds :
  ((cotangentSumVFormula_40_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 23 ∧
  cotangentSumVFormula 40 23 ≤ ((cotangentSumVFormula_40_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_23_unfold]
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
  rw [cotangentSumVFormula_40_23_lower, cotangentSumVFormula_40_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2340_formula_bound :
  (((78280339135110892877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 40) ∧
  (vasyuninBEntryFormula 23 40 ≤ ((78284842734741138373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_23_40_bounds
  have b_Vkh := cotangentSumVFormula_40_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_23_40_lower, cotangentSumVFormula_23_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_23_lower, cotangentSumVFormula_40_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_27_40_unfold :
    cotangentSumVFormula 27 40 =
      ((27/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 27 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_27_40_lower : ℚ := -1402830295262181276729 / 439804651110400000000
def cotangentSumVFormula_27_40_upper : ℚ := -1402830286465879660771 / 439804651110400000000
theorem cotangentSumVFormula_27_40_bounds :
  ((cotangentSumVFormula_27_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 27 40 ∧
  cotangentSumVFormula 27 40 ≤ ((cotangentSumVFormula_27_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_27_40_unfold]
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
  rw [cotangentSumVFormula_27_40_lower, cotangentSumVFormula_27_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_27_unfold :
    cotangentSumVFormula 40 27 =
      ((13/27 : ℚ) : ℝ) * cotangentTermV 1 27    + 
      ((26/27 : ℚ) : ℝ) * cotangentTermV 2 27    + 
      ((12/27 : ℚ) : ℝ) * cotangentTermV 3 27    + 
      ((25/27 : ℚ) : ℝ) * cotangentTermV 4 27    + 
      ((11/27 : ℚ) : ℝ) * cotangentTermV 5 27    + 
      ((24/27 : ℚ) : ℝ) * cotangentTermV 6 27    + 
      ((10/27 : ℚ) : ℝ) * cotangentTermV 7 27    + 
      ((23/27 : ℚ) : ℝ) * cotangentTermV 8 27    + 
      ((9/27 : ℚ) : ℝ) * cotangentTermV 9 27    + 
      ((22/27 : ℚ) : ℝ) * cotangentTermV 10 27    + 
      ((8/27 : ℚ) : ℝ) * cotangentTermV 11 27    + 
      ((21/27 : ℚ) : ℝ) * cotangentTermV 12 27    + 
      ((7/27 : ℚ) : ℝ) * cotangentTermV 13 27    + 
      ((20/27 : ℚ) : ℝ) * cotangentTermV 14 27    + 
      ((6/27 : ℚ) : ℝ) * cotangentTermV 15 27    + 
      ((19/27 : ℚ) : ℝ) * cotangentTermV 16 27    + 
      ((5/27 : ℚ) : ℝ) * cotangentTermV 17 27    + 
      ((18/27 : ℚ) : ℝ) * cotangentTermV 18 27    + 
      ((4/27 : ℚ) : ℝ) * cotangentTermV 19 27    + 
      ((17/27 : ℚ) : ℝ) * cotangentTermV 20 27    + 
      ((3/27 : ℚ) : ℝ) * cotangentTermV 21 27    + 
      ((16/27 : ℚ) : ℝ) * cotangentTermV 22 27    + 
      ((2/27 : ℚ) : ℝ) * cotangentTermV 23 27    + 
      ((15/27 : ℚ) : ℝ) * cotangentTermV 24 27    + 
      ((1/27 : ℚ) : ℝ) * cotangentTermV 25 27    + 
      ((14/27 : ℚ) : ℝ) * cotangentTermV 26 27 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_27]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((13/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((26/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((12/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((25/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((11/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((24/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((10/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((23/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((9/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((22/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((8/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((21/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((7/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((20/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((6/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((19/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((5/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((18/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((4/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((17/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((3/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((16/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((2/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((15/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((1/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((14/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26]
  try ring

def cotangentSumVFormula_40_27_lower : ℚ := 2609166837430207785771 / 439804651110400000000
def cotangentSumVFormula_40_27_upper : ℚ := 2609166846226398464229 / 439804651110400000000
theorem cotangentSumVFormula_40_27_bounds :
  ((cotangentSumVFormula_40_27_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 27 ∧
  cotangentSumVFormula 40 27 ≤ ((cotangentSumVFormula_40_27_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_27_unfold]
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
  rw [cotangentSumVFormula_40_27_lower, cotangentSumVFormula_40_27_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2740_formula_bound :
  (((18435451628948031813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 27 40) ∧
  (vasyuninBEntryFormula 27 40 ≤ ((18436577528855499437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 27 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log27 := prim_log_27_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_27_40_bounds
  have b_Vkh := cotangentSumVFormula_40_27_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_27_lower, prim_log_27_upper] at b_log27
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_27_40_lower, cotangentSumVFormula_27_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_27_lower, cotangentSumVFormula_40_27_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_40_unfold :
    cotangentSumVFormula 29 40 =
      ((29/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_29_40_lower : ℚ := 1033309835150911510073 / 219902325555200000000
def cotangentSumVFormula_29_40_upper : ℚ := 516654919774532330901 / 109951162777600000000
theorem cotangentSumVFormula_29_40_bounds :
  ((cotangentSumVFormula_29_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 40 ∧
  cotangentSumVFormula 29 40 ≤ ((cotangentSumVFormula_29_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_40_unfold]
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
  rw [cotangentSumVFormula_29_40_lower, cotangentSumVFormula_29_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_29_unfold :
    cotangentSumVFormula 40 29 =
      ((11/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_40_29_lower : ℚ := -1404425415048153569083 / 879609302220800000000
def cotangentSumVFormula_40_29_upper : ℚ := -1404425397455749555917 / 879609302220800000000
theorem cotangentSumVFormula_40_29_bounds :
  ((cotangentSumVFormula_40_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 29 ∧
  cotangentSumVFormula 40 29 ≤ ((cotangentSumVFormula_40_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_29_unfold]
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
  rw [cotangentSumVFormula_40_29_lower, cotangentSumVFormula_40_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2940_formula_bound :
  (((71533203039574080377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 40) ∧
  (vasyuninBEntryFormula 29 40 ≤ ((71537706639203919623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_29_40_bounds
  have b_Vkh := cotangentSumVFormula_40_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_29_40_lower, cotangentSumVFormula_29_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_29_lower, cotangentSumVFormula_40_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_40_unfold :
    cotangentSumVFormula 31 40 =
      ((31/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_31_40_lower : ℚ := 691514055092756731599 / 109951162777600000000
def cotangentSumVFormula_31_40_upper : ℚ := 345757028645914017013 / 54975581388800000000
theorem cotangentSumVFormula_31_40_bounds :
  ((cotangentSumVFormula_31_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 40 ∧
  cotangentSumVFormula 31 40 ≤ ((cotangentSumVFormula_31_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_40_unfold]
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
  rw [cotangentSumVFormula_31_40_lower, cotangentSumVFormula_31_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_31_unfold :
    cotangentSumVFormula 40 31 =
      ((9/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 40 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_40_31_lower : ℚ := -2727075614462130131583 / 879609302220800000000
def cotangentSumVFormula_40_31_upper : ℚ := -2727075596869640180917 / 879609302220800000000
theorem cotangentSumVFormula_40_31_bounds :
  ((cotangentSumVFormula_40_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 31 ∧
  cotangentSumVFormula 40 31 ≤ ((cotangentSumVFormula_40_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_31_unfold]
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
  rw [cotangentSumVFormula_40_31_lower, cotangentSumVFormula_40_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3140_formula_bound :
  (((140178248833113613879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 40) ∧
  (vasyuninBEntryFormula 31 40 ≤ ((140187256032373261121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_31_40_bounds
  have b_Vkh := cotangentSumVFormula_40_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_31_40_lower, cotangentSumVFormula_31_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_31_lower, cotangentSumVFormula_40_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_33_40_unfold :
    cotangentSumVFormula 33 40 =
      ((33/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 33 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_33_40_lower : ℚ := 1970432544109705260073 / 219902325555200000000
def cotangentSumVFormula_33_40_upper : ℚ := 1970432548507846302427 / 219902325555200000000
theorem cotangentSumVFormula_33_40_bounds :
  ((cotangentSumVFormula_33_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 40 ∧
  cotangentSumVFormula 33 40 ≤ ((cotangentSumVFormula_33_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_40_unfold]
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
  rw [cotangentSumVFormula_33_40_lower, cotangentSumVFormula_33_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_33_unfold :
    cotangentSumVFormula 40 33 =
      ((7/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((14/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((2/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((16/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((13/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((10/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((17/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((5/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 40 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_40_33_lower : ℚ := -1288650059450818177427 / 219902325555200000000
def cotangentSumVFormula_40_33_upper : ℚ := -1288650055052699010073 / 219902325555200000000
theorem cotangentSumVFormula_40_33_bounds :
  ((cotangentSumVFormula_40_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 33 ∧
  cotangentSumVFormula 40 33 ≤ ((cotangentSumVFormula_40_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_33_unfold]
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
  rw [cotangentSumVFormula_40_33_lower, cotangentSumVFormula_40_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3340_formula_bound :
  (((4314823929642441547 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 40) ∧
  (vasyuninBEntryFormula 33 40 ≤ ((69041686473908638373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_33_40_bounds
  have b_Vkh := cotangentSumVFormula_40_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_33_40_lower, cotangentSumVFormula_33_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_33_lower, cotangentSumVFormula_40_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_40_unfold :
    cotangentSumVFormula 37 40 =
      ((37/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((39/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_37_40_lower : ℚ := 60775608978250808507 / 3435973836800000000
def cotangentSumVFormula_37_40_upper : ℚ := 972409744751545267013 / 54975581388800000000
theorem cotangentSumVFormula_37_40_bounds :
  ((cotangentSumVFormula_37_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 40 ∧
  cotangentSumVFormula 37 40 ≤ ((cotangentSumVFormula_37_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_40_unfold]
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
  rw [cotangentSumVFormula_37_40_lower, cotangentSumVFormula_37_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_37_unfold :
    cotangentSumVFormula 40 37 =
      ((3/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 40 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_40_37_lower : ℚ := -3408461111432785364927 / 219902325555200000000
def cotangentSumVFormula_40_37_upper : ℚ := -3408461107034641978823 / 219902325555200000000
theorem cotangentSumVFormula_40_37_bounds :
  ((cotangentSumVFormula_40_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 37 ∧
  cotangentSumVFormula 40 37 ≤ ((cotangentSumVFormula_40_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_37_unfold]
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
  rw [cotangentSumVFormula_40_37_lower, cotangentSumVFormula_40_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3740_formula_bound :
  (((136872650413043457629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 40) ∧
  (vasyuninBEntryFormula 37 40 ≤ ((136881657612302417371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_37_40_bounds
  have b_Vkh := cotangentSumVFormula_40_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_37_40_lower, cotangentSumVFormula_37_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_37_lower, cotangentSumVFormula_40_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_39_40_unfold :
    cotangentSumVFormula 39 40 =
      ((39/40 : ℚ) : ℝ) * cotangentTermV 1 40    + 
      ((38/40 : ℚ) : ℝ) * cotangentTermV 2 40    + 
      ((37/40 : ℚ) : ℝ) * cotangentTermV 3 40    + 
      ((36/40 : ℚ) : ℝ) * cotangentTermV 4 40    + 
      ((35/40 : ℚ) : ℝ) * cotangentTermV 5 40    + 
      ((34/40 : ℚ) : ℝ) * cotangentTermV 6 40    + 
      ((33/40 : ℚ) : ℝ) * cotangentTermV 7 40    + 
      ((32/40 : ℚ) : ℝ) * cotangentTermV 8 40    + 
      ((31/40 : ℚ) : ℝ) * cotangentTermV 9 40    + 
      ((30/40 : ℚ) : ℝ) * cotangentTermV 10 40    + 
      ((29/40 : ℚ) : ℝ) * cotangentTermV 11 40    + 
      ((28/40 : ℚ) : ℝ) * cotangentTermV 12 40    + 
      ((27/40 : ℚ) : ℝ) * cotangentTermV 13 40    + 
      ((26/40 : ℚ) : ℝ) * cotangentTermV 14 40    + 
      ((25/40 : ℚ) : ℝ) * cotangentTermV 15 40    + 
      ((24/40 : ℚ) : ℝ) * cotangentTermV 16 40    + 
      ((23/40 : ℚ) : ℝ) * cotangentTermV 17 40    + 
      ((22/40 : ℚ) : ℝ) * cotangentTermV 18 40    + 
      ((21/40 : ℚ) : ℝ) * cotangentTermV 19 40    + 
      ((20/40 : ℚ) : ℝ) * cotangentTermV 20 40    + 
      ((19/40 : ℚ) : ℝ) * cotangentTermV 21 40    + 
      ((18/40 : ℚ) : ℝ) * cotangentTermV 22 40    + 
      ((17/40 : ℚ) : ℝ) * cotangentTermV 23 40    + 
      ((16/40 : ℚ) : ℝ) * cotangentTermV 24 40    + 
      ((15/40 : ℚ) : ℝ) * cotangentTermV 25 40    + 
      ((14/40 : ℚ) : ℝ) * cotangentTermV 26 40    + 
      ((13/40 : ℚ) : ℝ) * cotangentTermV 27 40    + 
      ((12/40 : ℚ) : ℝ) * cotangentTermV 28 40    + 
      ((11/40 : ℚ) : ℝ) * cotangentTermV 29 40    + 
      ((10/40 : ℚ) : ℝ) * cotangentTermV 30 40    + 
      ((9/40 : ℚ) : ℝ) * cotangentTermV 31 40    + 
      ((8/40 : ℚ) : ℝ) * cotangentTermV 32 40    + 
      ((7/40 : ℚ) : ℝ) * cotangentTermV 33 40    + 
      ((6/40 : ℚ) : ℝ) * cotangentTermV 34 40    + 
      ((5/40 : ℚ) : ℝ) * cotangentTermV 35 40    + 
      ((4/40 : ℚ) : ℝ) * cotangentTermV 36 40    + 
      ((3/40 : ℚ) : ℝ) * cotangentTermV 37 40    + 
      ((2/40 : ℚ) : ℝ) * cotangentTermV 38 40    + 
      ((1/40 : ℚ) : ℝ) * cotangentTermV 39 40 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_40]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 39 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_39_40_lower : ℚ := 1717301038991347701737 / 54975581388800000000
def cotangentSumVFormula_39_40_upper : ℚ := 1717301040090889017013 / 54975581388800000000
theorem cotangentSumVFormula_39_40_bounds :
  ((cotangentSumVFormula_39_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 40 ∧
  cotangentSumVFormula 39 40 ≤ ((cotangentSumVFormula_39_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_40_unfold]
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
  rw [cotangentSumVFormula_39_40_lower, cotangentSumVFormula_39_40_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_40_39_unfold :
    cotangentSumVFormula 40 39 =
      ((1/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 40 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_40_39_lower : ℚ := -414383346240683094097 / 13743895347200000000
def cotangentSumVFormula_40_39_upper : ℚ := -414383345965797374653 / 13743895347200000000
theorem cotangentSumVFormula_40_39_bounds :
  ((cotangentSumVFormula_40_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 39 ∧
  cotangentSumVFormula 40 39 ≤ ((cotangentSumVFormula_40_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_39_unfold]
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
  rw [cotangentSumVFormula_40_39_lower, cotangentSumVFormula_40_39_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3940_formula_bound :
  (((138786471353166238879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 39 40) ∧
  (vasyuninBEntryFormula 39 40 ≤ ((138795478552426386121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 39 40 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log39 := prim_log_39_bounds
  have b_log40 := prim_log_40_bounds
  have b_Vhk := cotangentSumVFormula_39_40_bounds
  have b_Vkh := cotangentSumVFormula_40_39_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [cotangentSumVFormula_39_40_lower, cotangentSumVFormula_39_40_upper] at b_Vhk
  simp only [cotangentSumVFormula_40_39_lower, cotangentSumVFormula_40_39_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
