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

theorem cotangentSumVFormula_31_38_unfold :
    cotangentSumVFormula 31 38 =
      ((31/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_31_38_lower : ℚ := 1668681313184545103823 / 219902325555200000000
def cotangentSumVFormula_31_38_upper : ℚ := 52146291174458929861 / 6871947673600000000
theorem cotangentSumVFormula_31_38_bounds :
  ((cotangentSumVFormula_31_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 38 ∧
  cotangentSumVFormula 31 38 ≤ ((cotangentSumVFormula_31_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_38_unfold]
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
  rw [cotangentSumVFormula_31_38_lower, cotangentSumVFormula_31_38_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_38_31_unfold :
    cotangentSumVFormula 38 31 =
      ((7/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_38_31_lower : ℚ := -2028696106145685964229 / 439804651110400000000
def cotangentSumVFormula_38_31_upper : ℚ := -2028696097349432004521 / 439804651110400000000
theorem cotangentSumVFormula_38_31_bounds :
  ((cotangentSumVFormula_38_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 31 ∧
  cotangentSumVFormula 38 31 ≤ ((cotangentSumVFormula_38_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_31_unfold]
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
  rw [cotangentSumVFormula_38_31_lower, cotangentSumVFormula_38_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3138_formula_bound :
  (((72839492882202549127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 38) ∧
  (vasyuninBEntryFormula 31 38 ≤ ((72843996481832513373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 38 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log38 := prim_log_38_bounds
  have b_Vhk := cotangentSumVFormula_31_38_bounds
  have b_Vkh := cotangentSumVFormula_38_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [cotangentSumVFormula_31_38_lower, cotangentSumVFormula_31_38_upper] at b_Vhk
  simp only [cotangentSumVFormula_38_31_lower, cotangentSumVFormula_38_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_33_38_unfold :
    cotangentSumVFormula 33 38 =
      ((33/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 33 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_33_38_lower : ℚ := 2405790475529157603823 / 219902325555200000000
def cotangentSumVFormula_33_38_upper : ℚ := 2405790479927292396177 / 219902325555200000000
theorem cotangentSumVFormula_33_38_bounds :
  ((cotangentSumVFormula_33_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 38 ∧
  cotangentSumVFormula 33 38 ≤ ((cotangentSumVFormula_33_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_38_unfold]
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
  rw [cotangentSumVFormula_33_38_lower, cotangentSumVFormula_33_38_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_38_33_unfold :
    cotangentSumVFormula 38 33 =
      ((5/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((10/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((2/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((7/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((17/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((14/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((16/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((13/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_38_33_lower : ℚ := -1810795136453606458677 / 219902325555200000000
def cotangentSumVFormula_38_33_upper : ℚ := -1810795132055484947573 / 219902325555200000000
theorem cotangentSumVFormula_38_33_bounds :
  ((cotangentSumVFormula_38_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 33 ∧
  cotangentSumVFormula 38 33 ≤ ((cotangentSumVFormula_38_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_33_unfold]
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
  rw [cotangentSumVFormula_38_33_lower, cotangentSumVFormula_38_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3338_formula_bound :
  (((36047997906984641751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 38) ∧
  (vasyuninBEntryFormula 33 38 ≤ ((36050249706799483249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 38 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log38 := prim_log_38_bounds
  have b_Vhk := cotangentSumVFormula_33_38_bounds
  have b_Vkh := cotangentSumVFormula_38_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [cotangentSumVFormula_33_38_lower, cotangentSumVFormula_33_38_upper] at b_Vhk
  simp only [cotangentSumVFormula_38_33_lower, cotangentSumVFormula_38_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_35_38_unfold :
    cotangentSumVFormula 35 38 =
      ((35/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 35 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_35_38_lower : ℚ := 912902922835849264237 / 54975581388800000000
def cotangentSumVFormula_35_38_upper : ℚ := 456451461967690797569 / 27487790694400000000
theorem cotangentSumVFormula_35_38_bounds :
  ((cotangentSumVFormula_35_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 38 ∧
  cotangentSumVFormula 35 38 ≤ ((cotangentSumVFormula_35_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_38_unfold]
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
  rw [cotangentSumVFormula_35_38_lower, cotangentSumVFormula_35_38_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_38_35_unfold :
    cotangentSumVFormula 38 35 =
      ((3/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 38 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_38_35_lower : ℚ := -3181625325755732239927 / 219902325555200000000
def cotangentSumVFormula_38_35_upper : ℚ := -3181625321357584166323 / 219902325555200000000
theorem cotangentSumVFormula_38_35_bounds :
  ((cotangentSumVFormula_38_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 35 ∧
  cotangentSumVFormula 38 35 ≤ ((cotangentSumVFormula_38_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_35_unfold]
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
  rw [cotangentSumVFormula_38_35_lower, cotangentSumVFormula_38_35_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3538_formula_bound :
  (((18002660650595375563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 35 38) ∧
  (vasyuninBEntryFormula 35 38 ≤ ((9001893275251413781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 35 38 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log35 := prim_log_35_bounds
  have b_log38 := prim_log_38_bounds
  have b_Vhk := cotangentSumVFormula_35_38_bounds
  have b_Vkh := cotangentSumVFormula_38_35_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [cotangentSumVFormula_35_38_lower, cotangentSumVFormula_35_38_upper] at b_Vhk
  simp only [cotangentSumVFormula_38_35_lower, cotangentSumVFormula_38_35_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_38_unfold :
    cotangentSumVFormula 37 38 =
      ((37/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_37_38_lower : ℚ := 3196429277981409075349 / 109951162777600000000
def cotangentSumVFormula_37_38_upper : ℚ := 3196429280180480768401 / 109951162777600000000
theorem cotangentSumVFormula_37_38_bounds :
  ((cotangentSumVFormula_37_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 38 ∧
  cotangentSumVFormula 37 38 ≤ ((cotangentSumVFormula_37_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_38_unfold]
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
  rw [cotangentSumVFormula_37_38_lower, cotangentSumVFormula_37_38_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_38_37_unfold :
    cotangentSumVFormula 38 37 =
      ((1/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 38 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_38_37_lower : ℚ := -1539356630453005423263 / 54975581388800000000
def cotangentSumVFormula_38_37_upper : ℚ := -769678314676734983681 / 27487790694400000000
theorem cotangentSumVFormula_38_37_bounds :
  ((cotangentSumVFormula_38_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 37 ∧
  cotangentSumVFormula 38 37 ≤ ((cotangentSumVFormula_38_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_37_unfold]
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
  rw [cotangentSumVFormula_38_37_lower, cotangentSumVFormula_38_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3738_formula_bound :
  (((72996647354362017877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 38) ∧
  (vasyuninBEntryFormula 37 38 ≤ ((73001150953991794623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 38 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log38 := prim_log_38_bounds
  have b_Vhk := cotangentSumVFormula_37_38_bounds
  have b_Vkh := cotangentSumVFormula_38_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [cotangentSumVFormula_37_38_lower, cotangentSumVFormula_37_38_upper] at b_Vhk
  simp only [cotangentSumVFormula_38_37_lower, cotangentSumVFormula_38_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_39_unfold :
    cotangentSumVFormula 1 39 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_1_39_lower : ℚ := -414383346240683094097 / 13743895347200000000
def cotangentSumVFormula_1_39_upper : ℚ := -414383345965797374653 / 13743895347200000000
theorem cotangentSumVFormula_1_39_bounds :
  ((cotangentSumVFormula_1_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 39 ∧
  cotangentSumVFormula 1 39 ≤ ((cotangentSumVFormula_1_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_39_unfold]
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
  rw [cotangentSumVFormula_1_39_lower, cotangentSumVFormula_1_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_1_unfold :
    cotangentSumVFormula 39 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_39_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_39_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_39_1_bounds :
  ((cotangentSumVFormula_39_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 1 ∧
  cotangentSumVFormula 39 1 ≤ ((cotangentSumVFormula_39_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_1_unfold]
  rw [cotangentSumVFormula_39_1_lower, cotangentSumVFormula_39_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_139_formula_bound :
  (((85614213818564454251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 39) ∧
  (vasyuninBEntryFormula 1 39 ≤ ((85616465618408545749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_1_39_bounds
  have b_Vkh := cotangentSumVFormula_39_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_1_39_lower, cotangentSumVFormula_1_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_1_lower, cotangentSumVFormula_39_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_39_unfold :
    cotangentSumVFormula 2 39 =
      ((2/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 2 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_2_39_lower : ℚ := -1201794960247885892013 / 54975581388800000000
def cotangentSumVFormula_2_39_upper : ℚ := -1201794959148343014237 / 54975581388800000000
theorem cotangentSumVFormula_2_39_bounds :
  ((cotangentSumVFormula_2_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 39 ∧
  cotangentSumVFormula 2 39 ≤ ((cotangentSumVFormula_2_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_39_unfold]
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
  rw [cotangentSumVFormula_2_39_lower, cotangentSumVFormula_2_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_2_unfold :
    cotangentSumVFormula 39 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_39_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_39_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_39_2_bounds :
  ((cotangentSumVFormula_39_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 2 ∧
  cotangentSumVFormula 39 2 ≤ ((cotangentSumVFormula_39_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_39_2_lower, cotangentSumVFormula_39_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_239_formula_bound :
  (((18870523776269179969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 39) ∧
  (vasyuninBEntryFormula 2 39 ≤ ((18871086726226320031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_2_39_bounds
  have b_Vkh := cotangentSumVFormula_39_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_2_39_lower, cotangentSumVFormula_2_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_2_lower, cotangentSumVFormula_39_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_39_unfold :
    cotangentSumVFormula 4 39 =
      ((4/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 4 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_4_39_lower : ℚ := -791021376373308548263 / 54975581388800000000
def cotangentSumVFormula_4_39_upper : ℚ := -1582042750547530950349 / 109951162777600000000
theorem cotangentSumVFormula_4_39_bounds :
  ((cotangentSumVFormula_4_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 39 ∧
  cotangentSumVFormula 4 39 ≤ ((cotangentSumVFormula_4_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_39_unfold]
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
  rw [cotangentSumVFormula_4_39_lower, cotangentSumVFormula_4_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_4_unfold :
    cotangentSumVFormula 39 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_39_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_39_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_39_4_bounds :
  ((cotangentSumVFormula_39_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 4 ∧
  cotangentSumVFormula 39 4 ≤ ((cotangentSumVFormula_39_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_39_4_lower, cotangentSumVFormula_39_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_439_formula_bound :
  (((130893668454403361627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 39) ∧
  (vasyuninBEntryFormula 4 39 ≤ ((130898172054045388373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_4_39_bounds
  have b_Vkh := cotangentSumVFormula_39_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_4_39_lower, cotangentSumVFormula_4_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_4_lower, cotangentSumVFormula_39_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_39_unfold :
    cotangentSumVFormula 5 39 =
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
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 5 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_5_39_lower : ℚ := -2711145537912431458677 / 219902325555200000000
def cotangentSumVFormula_5_39_upper : ℚ := -2711145533514260728823 / 219902325555200000000
theorem cotangentSumVFormula_5_39_bounds :
  ((cotangentSumVFormula_5_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 39 ∧
  cotangentSumVFormula 5 39 ≤ ((cotangentSumVFormula_5_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_39_unfold]
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
  rw [cotangentSumVFormula_5_39_lower, cotangentSumVFormula_5_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_5_unfold :
    cotangentSumVFormula 39 5 =
      ((4/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_39_5_lower : ℚ := 3134269892212533770543 / 3518437208883200000000
def cotangentSumVFormula_39_5_upper : ℚ := 3134269962581292010707 / 3518437208883200000000
theorem cotangentSumVFormula_39_5_bounds :
  ((cotangentSumVFormula_39_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 5 ∧
  cotangentSumVFormula 39 5 ≤ ((cotangentSumVFormula_39_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_39_5_lower, cotangentSumVFormula_39_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_539_formula_bound :
  (((31124199076381750563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 39) ∧
  (vasyuninBEntryFormula 5 39 ≤ ((15562662488145757531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_5_39_bounds
  have b_Vkh := cotangentSumVFormula_39_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_5_39_lower, cotangentSumVFormula_5_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_5_lower, cotangentSumVFormula_39_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_39_unfold :
    cotangentSumVFormula 7 39 =
      ((7/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_7_39_lower : ℚ := -1692605911470720521177 / 219902325555200000000
def cotangentSumVFormula_7_39_upper : ℚ := -846302953536277044099 / 109951162777600000000
theorem cotangentSumVFormula_7_39_bounds :
  ((cotangentSumVFormula_7_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 39 ∧
  cotangentSumVFormula 7 39 ≤ ((cotangentSumVFormula_7_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_39_unfold]
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
  rw [cotangentSumVFormula_7_39_lower, cotangentSumVFormula_7_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_7_unfold :
    cotangentSumVFormula 39 7 =
      ((4/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_39_7_lower : ℚ := -2465148184743653589703 / 14073748835532800000000
def cotangentSumVFormula_39_7_upper : ℚ := -2465147903268565160297 / 14073748835532800000000
theorem cotangentSumVFormula_39_7_bounds :
  ((cotangentSumVFormula_39_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 7 ∧
  cotangentSumVFormula 39 7 ≤ ((cotangentSumVFormula_39_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_7_unfold]
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
  rw [cotangentSumVFormula_39_7_lower, cotangentSumVFormula_39_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_739_formula_bound :
  (((7154516884755254047 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 39) ∧
  (vasyuninBEntryFormula 7 39 ≤ ((57238386877859670749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_7_39_bounds
  have b_Vkh := cotangentSumVFormula_39_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_7_39_lower, cotangentSumVFormula_7_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_7_lower, cotangentSumVFormula_39_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_39_unfold :
    cotangentSumVFormula 8 39 =
      ((8/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 8 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_8_39_lower : ℚ := -494406505933667142013 / 54975581388800000000
def cotangentSumVFormula_8_39_upper : ℚ := -988813009668252825349 / 109951162777600000000
theorem cotangentSumVFormula_8_39_bounds :
  ((cotangentSumVFormula_8_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 39 ∧
  cotangentSumVFormula 8 39 ≤ ((cotangentSumVFormula_8_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_39_unfold]
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
  rw [cotangentSumVFormula_8_39_lower, cotangentSumVFormula_8_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_8_unfold :
    cotangentSumVFormula 39 8 =
      ((7/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_39_8_lower : ℚ := 2123564698214891743417 / 879609302220800000000
def cotangentSumVFormula_39_8_upper : ℚ := 2123564715807086381583 / 879609302220800000000
theorem cotangentSumVFormula_39_8_bounds :
  ((cotangentSumVFormula_39_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 8 ∧
  cotangentSumVFormula 39 8 ≤ ((cotangentSumVFormula_39_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_8_unfold]
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
  rw [cotangentSumVFormula_39_8_lower, cotangentSumVFormula_39_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_839_formula_bound :
  (((111187091248250830377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 39) ∧
  (vasyuninBEntryFormula 8 39 ≤ ((111191594847884888373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_8_39_bounds
  have b_Vkh := cotangentSumVFormula_39_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_8_39_lower, cotangentSumVFormula_8_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_8_lower, cotangentSumVFormula_39_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_39_unfold :
    cotangentSumVFormula 10 39 =
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
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 10 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_10_39_lower : ℚ := -446323646027439017013 / 54975581388800000000
def cotangentSumVFormula_10_39_upper : ℚ := -111580911231974718403 / 13743895347200000000
theorem cotangentSumVFormula_10_39_bounds :
  ((cotangentSumVFormula_10_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 39 ∧
  cotangentSumVFormula 10 39 ≤ ((cotangentSumVFormula_10_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_39_unfold]
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
  rw [cotangentSumVFormula_10_39_lower, cotangentSumVFormula_10_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_10_unfold :
    cotangentSumVFormula 39 10 =
      ((9/10 : ℚ) : ℝ) * cotangentTermV 1 10    + 
      ((8/10 : ℚ) : ℝ) * cotangentTermV 2 10    + 
      ((7/10 : ℚ) : ℝ) * cotangentTermV 3 10    + 
      ((6/10 : ℚ) : ℝ) * cotangentTermV 4 10    + 
      ((5/10 : ℚ) : ℝ) * cotangentTermV 5 10    + 
      ((4/10 : ℚ) : ℝ) * cotangentTermV 6 10    + 
      ((3/10 : ℚ) : ℝ) * cotangentTermV 7 10    + 
      ((2/10 : ℚ) : ℝ) * cotangentTermV 8 10    + 
      ((1/10 : ℚ) : ℝ) * cotangentTermV 9 10 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_10]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_39_10_lower : ℚ := 3204924154363070649667 / 879609302220800000000
def cotangentSumVFormula_39_10_upper : ℚ := 3204924171955274662833 / 879609302220800000000
theorem cotangentSumVFormula_39_10_bounds :
  ((cotangentSumVFormula_39_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 10 ∧
  cotangentSumVFormula 39 10 ≤ ((cotangentSumVFormula_39_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_10_unfold]
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
  rw [cotangentSumVFormula_39_10_lower, cotangentSumVFormula_39_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1039_formula_bound :
  (((104974128934227611627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 39) ∧
  (vasyuninBEntryFormula 10 39 ≤ ((104978632533860419623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_10_39_bounds
  have b_Vkh := cotangentSumVFormula_39_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_10_39_lower, cotangentSumVFormula_10_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_10_lower, cotangentSumVFormula_39_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_39_unfold :
    cotangentSumVFormula 11 39 =
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
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_11_39_lower : ℚ := -279675822909583112151 / 109951162777600000000
def cotangentSumVFormula_11_39_upper : ℚ := -559351641420995885073 / 219902325555200000000
theorem cotangentSumVFormula_11_39_bounds :
  ((cotangentSumVFormula_11_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 39 ∧
  cotangentSumVFormula 11 39 ≤ ((cotangentSumVFormula_11_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_39_unfold]
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
  rw [cotangentSumVFormula_11_39_lower, cotangentSumVFormula_11_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_11_unfold :
    cotangentSumVFormula 39 11 =
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
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_39_11_lower : ℚ := -3351142826950507635707 / 3518437208883200000000
def cotangentSumVFormula_39_11_upper : ℚ := -3351142756581654864293 / 3518437208883200000000
theorem cotangentSumVFormula_39_11_bounds :
  ((cotangentSumVFormula_39_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 11 ∧
  cotangentSumVFormula 39 11 ≤ ((cotangentSumVFormula_39_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_11_unfold]
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
  rw [cotangentSumVFormula_39_11_lower, cotangentSumVFormula_39_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1139_formula_bound :
  (((101243965758527174127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 39) ∧
  (vasyuninBEntryFormula 11 39 ≤ ((101248469358159888373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_11_39_bounds
  have b_Vkh := cotangentSumVFormula_39_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_11_39_lower, cotangentSumVFormula_11_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_11_lower, cotangentSumVFormula_39_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_14_39_unfold :
    cotangentSumVFormula 14 39 =
      ((14/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 14 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_14_39_lower : ℚ := -3387833984007514506583 / 879609302220800000000
def cotangentSumVFormula_14_39_upper : ℚ := -3387833966414857368417 / 879609302220800000000
theorem cotangentSumVFormula_14_39_bounds :
  ((cotangentSumVFormula_14_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 39 ∧
  cotangentSumVFormula 14 39 ≤ ((cotangentSumVFormula_14_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_39_unfold]
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
  rw [cotangentSumVFormula_14_39_lower, cotangentSumVFormula_14_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_14_unfold :
    cotangentSumVFormula 39 14 =
      ((11/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((1/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((3/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_39_14_lower : ℚ := 2096053289555596430917 / 879609302220800000000
def cotangentSumVFormula_39_14_upper : ℚ := 2096053307147823881583 / 879609302220800000000
theorem cotangentSumVFormula_39_14_bounds :
  ((cotangentSumVFormula_39_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 14 ∧
  cotangentSumVFormula 39 14 ≤ ((cotangentSumVFormula_39_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_14_unfold]
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
  rw [cotangentSumVFormula_39_14_lower, cotangentSumVFormula_39_14_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1439_formula_bound :
  (((94474650842084517877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 14 39) ∧
  (vasyuninBEntryFormula 14 39 ≤ ((94479154441716013373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 14 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log14 := prim_log_14_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_14_39_bounds
  have b_Vkh := cotangentSumVFormula_39_14_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_14_39_lower, cotangentSumVFormula_14_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_14_lower, cotangentSumVFormula_39_14_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_16_39_unfold :
    cotangentSumVFormula 16 39 =
      ((16/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 16 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_16_39_lower : ℚ := -1754763313165433310041 / 1759218604441600000000
def cotangentSumVFormula_16_39_upper : ℚ := -1754763277980141689959 / 1759218604441600000000
theorem cotangentSumVFormula_16_39_bounds :
  ((cotangentSumVFormula_16_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 39 ∧
  cotangentSumVFormula 16 39 ≤ ((cotangentSumVFormula_16_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_39_unfold]
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
  rw [cotangentSumVFormula_16_39_lower, cotangentSumVFormula_16_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_16_unfold :
    cotangentSumVFormula 39 16 =
      ((7/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_39_16_lower : ℚ := 2226850521608540020543 / 3518437208883200000000
def cotangentSumVFormula_39_16_upper : ℚ := 2226850591977491229457 / 3518437208883200000000
theorem cotangentSumVFormula_39_16_bounds :
  ((cotangentSumVFormula_39_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 16 ∧
  cotangentSumVFormula 39 16 ≤ ((cotangentSumVFormula_39_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_16_unfold]
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
  rw [cotangentSumVFormula_39_16_lower, cotangentSumVFormula_39_16_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1639_formula_bound :
  (((90194769764901392877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 16 39) ∧
  (vasyuninBEntryFormula 16 39 ≤ ((90199273364532357123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 16 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log16 := prim_log_16_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_16_39_bounds
  have b_Vkh := cotangentSumVFormula_39_16_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_16_39_lower, cotangentSumVFormula_16_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_16_lower, cotangentSumVFormula_39_16_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_39_unfold :
    cotangentSumVFormula 17 39 =
      ((17/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_17_39_lower : ℚ := 576674907985681223271 / 439804651110400000000
def cotangentSumVFormula_17_39_upper : ℚ := 576674916781998464229 / 439804651110400000000
theorem cotangentSumVFormula_17_39_bounds :
  ((cotangentSumVFormula_17_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 39 ∧
  cotangentSumVFormula 17 39 ≤ ((cotangentSumVFormula_17_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_39_unfold]
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
  rw [cotangentSumVFormula_17_39_lower, cotangentSumVFormula_17_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_17_unfold :
    cotangentSumVFormula 39 17 =
      ((5/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_39_17_lower : ℚ := -2253702665312962997541 / 1759218604441600000000
def cotangentSumVFormula_39_17_upper : ℚ := -2253702630128444814959 / 1759218604441600000000
theorem cotangentSumVFormula_39_17_bounds :
  ((cotangentSumVFormula_39_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 17 ∧
  cotangentSumVFormula 39 17 ≤ ((cotangentSumVFormula_39_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_17_unfold]
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
  rw [cotangentSumVFormula_39_17_lower, cotangentSumVFormula_39_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1739_formula_bound :
  (((88702246823807361627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 39) ∧
  (vasyuninBEntryFormula 17 39 ≤ ((88706750423438200873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_17_39_bounds
  have b_Vkh := cotangentSumVFormula_39_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_17_39_lower, cotangentSumVFormula_17_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_17_lower, cotangentSumVFormula_39_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_39_unfold :
    cotangentSumVFormula 19 39 =
      ((19/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_19_39_lower : ℚ := 2369698197184604478823 / 219902325555200000000
def cotangentSumVFormula_19_39_upper : ℚ := 2369698201582761927427 / 219902325555200000000
theorem cotangentSumVFormula_19_39_bounds :
  ((cotangentSumVFormula_19_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 39 ∧
  cotangentSumVFormula 19 39 ≤ ((cotangentSumVFormula_19_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_39_unfold]
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
  rw [cotangentSumVFormula_19_39_lower, cotangentSumVFormula_19_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_19_unfold :
    cotangentSumVFormula 39 19 =
      ((1/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_39_19_lower : ℚ := -2310337804999529896177 / 219902325555200000000
def cotangentSumVFormula_39_19_upper : ℚ := -2310337800601460728823 / 219902325555200000000
theorem cotangentSumVFormula_39_19_bounds :
  ((cotangentSumVFormula_39_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 19 ∧
  cotangentSumVFormula 39 19 ≤ ((cotangentSumVFormula_39_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_19_unfold]
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
  rw [cotangentSumVFormula_39_19_lower, cotangentSumVFormula_39_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1939_formula_bound :
  (((21988621940661875563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 39) ∧
  (vasyuninBEntryFormula 19 39 ≤ ((10994873920284757531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_19_39_bounds
  have b_Vkh := cotangentSumVFormula_39_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_19_39_lower, cotangentSumVFormula_19_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_19_lower, cotangentSumVFormula_39_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_20_39_unfold :
    cotangentSumVFormula 20 39 =
      ((20/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 20 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_20_39_lower : ℚ := -2369698201582742396177 / 219902325555200000000
def cotangentSumVFormula_20_39_upper : ℚ := -2369698197184591197573 / 219902325555200000000
theorem cotangentSumVFormula_20_39_bounds :
  ((cotangentSumVFormula_20_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 39 ∧
  cotangentSumVFormula 20 39 ≤ ((cotangentSumVFormula_20_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_39_unfold]
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
  rw [cotangentSumVFormula_20_39_lower, cotangentSumVFormula_20_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_20_unfold :
    cotangentSumVFormula 39 20 =
      ((19/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((9/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_39_20_lower : ℚ := 1249977234199639544099 / 109951162777600000000
def cotangentSumVFormula_39_20_upper : ℚ := 624988618199335892013 / 54975581388800000000
theorem cotangentSumVFormula_39_20_bounds :
  ((cotangentSumVFormula_39_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 20 ∧
  cotangentSumVFormula 39 20 ≤ ((cotangentSumVFormula_39_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_20_unfold]
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
  rw [cotangentSumVFormula_39_20_lower, cotangentSumVFormula_39_20_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2039_formula_bound :
  (((86359154605947424127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 20 39) ∧
  (vasyuninBEntryFormula 20 39 ≤ ((86363658205577607123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 20 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log20 := prim_log_20_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_20_39_bounds
  have b_Vkh := cotangentSumVFormula_39_20_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_20_39_lower, cotangentSumVFormula_20_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_20_lower, cotangentSumVFormula_39_20_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_22_39_unfold :
    cotangentSumVFormula 22 39 =
      ((22/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 22 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_22_39_lower : ℚ := -2306699667127906747541 / 1759218604441600000000
def cotangentSumVFormula_22_39_upper : ℚ := -2306699631942615127459 / 1759218604441600000000
theorem cotangentSumVFormula_22_39_bounds :
  ((cotangentSumVFormula_22_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 22 39 ∧
  cotangentSumVFormula 22 39 ≤ ((cotangentSumVFormula_22_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_22_39_unfold]
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
  rw [cotangentSumVFormula_22_39_lower, cotangentSumVFormula_22_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_22_unfold :
    cotangentSumVFormula 39 22 =
      ((17/22 : ℚ) : ℝ) * cotangentTermV 1 22    + 
      ((12/22 : ℚ) : ℝ) * cotangentTermV 2 22    + 
      ((7/22 : ℚ) : ℝ) * cotangentTermV 3 22    + 
      ((2/22 : ℚ) : ℝ) * cotangentTermV 4 22    + 
      ((19/22 : ℚ) : ℝ) * cotangentTermV 5 22    + 
      ((14/22 : ℚ) : ℝ) * cotangentTermV 6 22    + 
      ((9/22 : ℚ) : ℝ) * cotangentTermV 7 22    + 
      ((4/22 : ℚ) : ℝ) * cotangentTermV 8 22    + 
      ((21/22 : ℚ) : ℝ) * cotangentTermV 9 22    + 
      ((16/22 : ℚ) : ℝ) * cotangentTermV 10 22    + 
      ((11/22 : ℚ) : ℝ) * cotangentTermV 11 22    + 
      ((6/22 : ℚ) : ℝ) * cotangentTermV 12 22    + 
      ((1/22 : ℚ) : ℝ) * cotangentTermV 13 22    + 
      ((18/22 : ℚ) : ℝ) * cotangentTermV 14 22    + 
      ((13/22 : ℚ) : ℝ) * cotangentTermV 15 22    + 
      ((8/22 : ℚ) : ℝ) * cotangentTermV 16 22    + 
      ((3/22 : ℚ) : ℝ) * cotangentTermV 17 22    + 
      ((20/22 : ℚ) : ℝ) * cotangentTermV 18 22    + 
      ((15/22 : ℚ) : ℝ) * cotangentTermV 19 22    + 
      ((10/22 : ℚ) : ℝ) * cotangentTermV 20 22    + 
      ((5/22 : ℚ) : ℝ) * cotangentTermV 21 22 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_22]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((17/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((12/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((7/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((2/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((19/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((14/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((9/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((4/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((21/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((16/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((11/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((6/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((1/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((18/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((13/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((8/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((3/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((20/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((15/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((10/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((5/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21]
  try ring

def cotangentSumVFormula_39_22_lower : ℚ := 2669102513321871430917 / 879609302220800000000
def cotangentSumVFormula_39_22_upper : ℚ := 2669102530914184819083 / 879609302220800000000
theorem cotangentSumVFormula_39_22_bounds :
  ((cotangentSumVFormula_39_22_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 22 ∧
  cotangentSumVFormula 39 22 ≤ ((cotangentSumVFormula_39_22_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_22_unfold]
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
  rw [cotangentSumVFormula_39_22_lower, cotangentSumVFormula_39_22_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2239_formula_bound :
  (((40516764762905423001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 22 39) ∧
  (vasyuninBEntryFormula 22 39 ≤ ((40519016562720608249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 22 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log22 := prim_log_22_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_22_39_bounds
  have b_Vkh := cotangentSumVFormula_39_22_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_22_lower, prim_log_22_upper] at b_log22
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_22_39_lower, cotangentSumVFormula_22_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_22_lower, cotangentSumVFormula_39_22_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_39_unfold :
    cotangentSumVFormula 23 39 =
      ((23/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_23_39_lower : ℚ := 3509526555960510333043 / 3518437208883200000000
def cotangentSumVFormula_23_39_upper : ℚ := 3509526626331077166957 / 3518437208883200000000
theorem cotangentSumVFormula_23_39_bounds :
  ((cotangentSumVFormula_23_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 39 ∧
  cotangentSumVFormula 23 39 ≤ ((cotangentSumVFormula_23_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_39_unfold]
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
  rw [cotangentSumVFormula_23_39_lower, cotangentSumVFormula_23_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_23_unfold :
    cotangentSumVFormula 39 23 =
      ((16/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_39_23_lower : ℚ := 1875425796061533096209 / 1759218604441600000000
def cotangentSumVFormula_39_23_upper : ℚ := 1875425831246207528791 / 1759218604441600000000
theorem cotangentSumVFormula_39_23_bounds :
  ((cotangentSumVFormula_39_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 23 ∧
  cotangentSumVFormula 39 23 ≤ ((cotangentSumVFormula_39_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_23_unfold]
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
  rw [cotangentSumVFormula_39_23_lower, cotangentSumVFormula_39_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2339_formula_bound :
  (((79361990087709080377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 39) ∧
  (vasyuninBEntryFormula 23 39 ≤ ((79366493687339450873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_23_39_bounds
  have b_Vkh := cotangentSumVFormula_39_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_23_39_lower, cotangentSumVFormula_23_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_23_lower, cotangentSumVFormula_39_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_25_39_unfold :
    cotangentSumVFormula 25 39 =
      ((25/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 25 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_25_39_lower : ℚ := 846958491603731041323 / 219902325555200000000
def cotangentSumVFormula_25_39_upper : ℚ := 423479248000943268401 / 109951162777600000000
theorem cotangentSumVFormula_25_39_bounds :
  ((cotangentSumVFormula_25_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 39 ∧
  cotangentSumVFormula 25 39 ≤ ((cotangentSumVFormula_25_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_39_unfold]
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
  rw [cotangentSumVFormula_25_39_lower, cotangentSumVFormula_25_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_25_unfold :
    cotangentSumVFormula 39 25 =
      ((14/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((17/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((12/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((21/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((24/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((19/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((22/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((11/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_39_25_lower : ℚ := -72541029136389798263 / 54975581388800000000
def cotangentSumVFormula_39_25_upper : ℚ := -580328224294939817021 / 439804651110400000000
theorem cotangentSumVFormula_39_25_bounds :
  ((cotangentSumVFormula_39_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 25 ∧
  cotangentSumVFormula 39 25 ≤ ((cotangentSumVFormula_39_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_25_unfold]
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
  rw [cotangentSumVFormula_39_25_lower, cotangentSumVFormula_39_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2539_formula_bound :
  (((76792426299398361627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 39) ∧
  (vasyuninBEntryFormula 25 39 ≤ ((76796929899028513373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_25_39_bounds
  have b_Vkh := cotangentSumVFormula_39_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_25_39_lower, cotangentSumVFormula_25_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_25_lower, cotangentSumVFormula_39_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_28_39_unfold :
    cotangentSumVFormula 28 39 =
      ((28/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 28 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_28_39_lower : ℚ := 2237406565684073774667 / 879609302220800000000
def cotangentSumVFormula_28_39_upper : ℚ := 2237406583276669975333 / 879609302220800000000
theorem cotangentSumVFormula_28_39_bounds :
  ((cotangentSumVFormula_28_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 28 39 ∧
  cotangentSumVFormula 28 39 ≤ ((cotangentSumVFormula_28_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_28_39_unfold]
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
  rw [cotangentSumVFormula_28_39_lower, cotangentSumVFormula_28_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_28_unfold :
    cotangentSumVFormula 39 28 =
      ((11/28 : ℚ) : ℝ) * cotangentTermV 1 28    + 
      ((22/28 : ℚ) : ℝ) * cotangentTermV 2 28    + 
      ((5/28 : ℚ) : ℝ) * cotangentTermV 3 28    + 
      ((16/28 : ℚ) : ℝ) * cotangentTermV 4 28    + 
      ((27/28 : ℚ) : ℝ) * cotangentTermV 5 28    + 
      ((10/28 : ℚ) : ℝ) * cotangentTermV 6 28    + 
      ((21/28 : ℚ) : ℝ) * cotangentTermV 7 28    + 
      ((4/28 : ℚ) : ℝ) * cotangentTermV 8 28    + 
      ((15/28 : ℚ) : ℝ) * cotangentTermV 9 28    + 
      ((26/28 : ℚ) : ℝ) * cotangentTermV 10 28    + 
      ((9/28 : ℚ) : ℝ) * cotangentTermV 11 28    + 
      ((20/28 : ℚ) : ℝ) * cotangentTermV 12 28    + 
      ((3/28 : ℚ) : ℝ) * cotangentTermV 13 28    + 
      ((14/28 : ℚ) : ℝ) * cotangentTermV 14 28    + 
      ((25/28 : ℚ) : ℝ) * cotangentTermV 15 28    + 
      ((8/28 : ℚ) : ℝ) * cotangentTermV 16 28    + 
      ((19/28 : ℚ) : ℝ) * cotangentTermV 17 28    + 
      ((2/28 : ℚ) : ℝ) * cotangentTermV 18 28    + 
      ((13/28 : ℚ) : ℝ) * cotangentTermV 19 28    + 
      ((24/28 : ℚ) : ℝ) * cotangentTermV 20 28    + 
      ((7/28 : ℚ) : ℝ) * cotangentTermV 21 28    + 
      ((18/28 : ℚ) : ℝ) * cotangentTermV 22 28    + 
      ((1/28 : ℚ) : ℝ) * cotangentTermV 23 28    + 
      ((12/28 : ℚ) : ℝ) * cotangentTermV 24 28    + 
      ((23/28 : ℚ) : ℝ) * cotangentTermV 25 28    + 
      ((6/28 : ℚ) : ℝ) * cotangentTermV 26 28    + 
      ((17/28 : ℚ) : ℝ) * cotangentTermV 27 28 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_28]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((11/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((22/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((5/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((16/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((27/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((10/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((21/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((4/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((15/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((26/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((9/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((20/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((3/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((14/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((25/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((8/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((19/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((2/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((13/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((24/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((7/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((18/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((1/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((12/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((23/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((6/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((17/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27]
  try ring

def cotangentSumVFormula_39_28_lower : ℚ := 3188508442640380431711 / 7036874417766400000000
def cotangentSumVFormula_39_28_upper : ℚ := 3188508583379744568289 / 7036874417766400000000
theorem cotangentSumVFormula_39_28_bounds :
  ((cotangentSumVFormula_39_28_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 28 ∧
  cotangentSumVFormula 39 28 ≤ ((cotangentSumVFormula_39_28_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_28_unfold]
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
  rw [cotangentSumVFormula_39_28_lower, cotangentSumVFormula_39_28_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2839_formula_bound :
  (((73619244205973986627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 28 39) ∧
  (vasyuninBEntryFormula 28 39 ≤ ((73623747805603919623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 28 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log28 := prim_log_28_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_28_39_bounds
  have b_Vkh := cotangentSumVFormula_39_28_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_28_lower, prim_log_28_upper] at b_log28
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_28_39_lower, cotangentSumVFormula_28_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_28_lower, cotangentSumVFormula_39_28_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_39_unfold :
    cotangentSumVFormula 29 39 =
      ((29/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_29_39_lower : ℚ := 892647289855808294099 / 109951162777600000000
def cotangentSumVFormula_29_39_upper : ℚ := 892647292054883112151 / 109951162777600000000
theorem cotangentSumVFormula_29_39_bounds :
  ((cotangentSumVFormula_29_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 39 ∧
  cotangentSumVFormula 29 39 ≤ ((cotangentSumVFormula_29_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_39_unfold]
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
  rw [cotangentSumVFormula_29_39_lower, cotangentSumVFormula_29_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_29_unfold :
    cotangentSumVFormula 39 29 =
      ((10/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_39_29_lower : ℚ := -2232956412637791432979 / 439804651110400000000
def cotangentSumVFormula_39_29_upper : ℚ := -2232956403841586692021 / 439804651110400000000
theorem cotangentSumVFormula_39_29_bounds :
  ((cotangentSumVFormula_39_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 29 ∧
  cotangentSumVFormula 39 29 ≤ ((cotangentSumVFormula_39_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_29_unfold]
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
  rw [cotangentSumVFormula_39_29_lower, cotangentSumVFormula_39_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2939_formula_bound :
  (((72875028686139205377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 39) ∧
  (vasyuninBEntryFormula 29 39 ≤ ((72879532285769044623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_29_39_bounds
  have b_Vkh := cotangentSumVFormula_39_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_29_39_lower, cotangentSumVFormula_29_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_29_lower, cotangentSumVFormula_39_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_39_unfold :
    cotangentSumVFormula 31 39 =
      ((31/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((32/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_31_39_lower : ℚ := 1977626019336527135073 / 219902325555200000000
def cotangentSumVFormula_31_39_upper : ℚ := 1977626023734675989927 / 219902325555200000000
theorem cotangentSumVFormula_31_39_bounds :
  ((cotangentSumVFormula_31_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 39 ∧
  cotangentSumVFormula 31 39 ≤ ((cotangentSumVFormula_31_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_39_unfold]
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
  rw [cotangentSumVFormula_31_39_lower, cotangentSumVFormula_31_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_31_unfold :
    cotangentSumVFormula 39 31 =
      ((8/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_39_31_lower : ℚ := -162380125774370485069 / 27487790694400000000
def cotangentSumVFormula_39_31_upper : ℚ := -1299041001796838072573 / 219902325555200000000
theorem cotangentSumVFormula_39_31_bounds :
  ((cotangentSumVFormula_39_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 31 ∧
  cotangentSumVFormula 39 31 ≤ ((cotangentSumVFormula_39_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_31_unfold]
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
  rw [cotangentSumVFormula_39_31_lower, cotangentSumVFormula_39_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3139_formula_bound :
  (((71439987259032736627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 39) ∧
  (vasyuninBEntryFormula 31 39 ≤ ((71444490858662732123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_31_39_bounds
  have b_Vkh := cotangentSumVFormula_39_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_31_39_lower, cotangentSumVFormula_31_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_31_lower, cotangentSumVFormula_39_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_32_39_unfold :
    cotangentSumVFormula 32 39 =
      ((32/39 : ℚ) : ℝ) * cotangentTermV 1 39    + 
      ((25/39 : ℚ) : ℝ) * cotangentTermV 2 39    + 
      ((18/39 : ℚ) : ℝ) * cotangentTermV 3 39    + 
      ((11/39 : ℚ) : ℝ) * cotangentTermV 4 39    + 
      ((4/39 : ℚ) : ℝ) * cotangentTermV 5 39    + 
      ((36/39 : ℚ) : ℝ) * cotangentTermV 6 39    + 
      ((29/39 : ℚ) : ℝ) * cotangentTermV 7 39    + 
      ((22/39 : ℚ) : ℝ) * cotangentTermV 8 39    + 
      ((15/39 : ℚ) : ℝ) * cotangentTermV 9 39    + 
      ((8/39 : ℚ) : ℝ) * cotangentTermV 10 39    + 
      ((1/39 : ℚ) : ℝ) * cotangentTermV 11 39    + 
      ((33/39 : ℚ) : ℝ) * cotangentTermV 12 39    + 
      ((26/39 : ℚ) : ℝ) * cotangentTermV 13 39    + 
      ((19/39 : ℚ) : ℝ) * cotangentTermV 14 39    + 
      ((12/39 : ℚ) : ℝ) * cotangentTermV 15 39    + 
      ((5/39 : ℚ) : ℝ) * cotangentTermV 16 39    + 
      ((37/39 : ℚ) : ℝ) * cotangentTermV 17 39    + 
      ((30/39 : ℚ) : ℝ) * cotangentTermV 18 39    + 
      ((23/39 : ℚ) : ℝ) * cotangentTermV 19 39    + 
      ((16/39 : ℚ) : ℝ) * cotangentTermV 20 39    + 
      ((9/39 : ℚ) : ℝ) * cotangentTermV 21 39    + 
      ((2/39 : ℚ) : ℝ) * cotangentTermV 22 39    + 
      ((34/39 : ℚ) : ℝ) * cotangentTermV 23 39    + 
      ((27/39 : ℚ) : ℝ) * cotangentTermV 24 39    + 
      ((20/39 : ℚ) : ℝ) * cotangentTermV 25 39    + 
      ((13/39 : ℚ) : ℝ) * cotangentTermV 26 39    + 
      ((6/39 : ℚ) : ℝ) * cotangentTermV 27 39    + 
      ((38/39 : ℚ) : ℝ) * cotangentTermV 28 39    + 
      ((31/39 : ℚ) : ℝ) * cotangentTermV 29 39    + 
      ((24/39 : ℚ) : ℝ) * cotangentTermV 30 39    + 
      ((17/39 : ℚ) : ℝ) * cotangentTermV 31 39    + 
      ((10/39 : ℚ) : ℝ) * cotangentTermV 32 39    + 
      ((3/39 : ℚ) : ℝ) * cotangentTermV 33 39    + 
      ((35/39 : ℚ) : ℝ) * cotangentTermV 34 39    + 
      ((28/39 : ℚ) : ℝ) * cotangentTermV 35 39    + 
      ((21/39 : ℚ) : ℝ) * cotangentTermV 36 39    + 
      ((14/39 : ℚ) : ℝ) * cotangentTermV 37 39    + 
      ((7/39 : ℚ) : ℝ) * cotangentTermV 38 39 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_39]
  have hf_1 : Int.fract (((1 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 32 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_32_39_lower : ℚ := 1692605907072583385073 / 219902325555200000000
def cotangentSumVFormula_32_39_upper : ℚ := 1692605911470726771177 / 219902325555200000000
theorem cotangentSumVFormula_32_39_bounds :
  ((cotangentSumVFormula_32_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 32 39 ∧
  cotangentSumVFormula 32 39 ≤ ((cotangentSumVFormula_32_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_32_39_unfold]
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
  rw [cotangentSumVFormula_32_39_lower, cotangentSumVFormula_32_39_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_39_32_unfold :
    cotangentSumVFormula 39 32 =
      ((7/32 : ℚ) : ℝ) * cotangentTermV 1 32    + 
      ((14/32 : ℚ) : ℝ) * cotangentTermV 2 32    + 
      ((21/32 : ℚ) : ℝ) * cotangentTermV 3 32    + 
      ((28/32 : ℚ) : ℝ) * cotangentTermV 4 32    + 
      ((3/32 : ℚ) : ℝ) * cotangentTermV 5 32    + 
      ((10/32 : ℚ) : ℝ) * cotangentTermV 6 32    + 
      ((17/32 : ℚ) : ℝ) * cotangentTermV 7 32    + 
      ((24/32 : ℚ) : ℝ) * cotangentTermV 8 32    + 
      ((31/32 : ℚ) : ℝ) * cotangentTermV 9 32    + 
      ((6/32 : ℚ) : ℝ) * cotangentTermV 10 32    + 
      ((13/32 : ℚ) : ℝ) * cotangentTermV 11 32    + 
      ((20/32 : ℚ) : ℝ) * cotangentTermV 12 32    + 
      ((27/32 : ℚ) : ℝ) * cotangentTermV 13 32    + 
      ((2/32 : ℚ) : ℝ) * cotangentTermV 14 32    + 
      ((9/32 : ℚ) : ℝ) * cotangentTermV 15 32    + 
      ((16/32 : ℚ) : ℝ) * cotangentTermV 16 32    + 
      ((23/32 : ℚ) : ℝ) * cotangentTermV 17 32    + 
      ((30/32 : ℚ) : ℝ) * cotangentTermV 18 32    + 
      ((5/32 : ℚ) : ℝ) * cotangentTermV 19 32    + 
      ((12/32 : ℚ) : ℝ) * cotangentTermV 20 32    + 
      ((19/32 : ℚ) : ℝ) * cotangentTermV 21 32    + 
      ((26/32 : ℚ) : ℝ) * cotangentTermV 22 32    + 
      ((1/32 : ℚ) : ℝ) * cotangentTermV 23 32    + 
      ((8/32 : ℚ) : ℝ) * cotangentTermV 24 32    + 
      ((15/32 : ℚ) : ℝ) * cotangentTermV 25 32    + 
      ((22/32 : ℚ) : ℝ) * cotangentTermV 26 32    + 
      ((29/32 : ℚ) : ℝ) * cotangentTermV 27 32    + 
      ((4/32 : ℚ) : ℝ) * cotangentTermV 28 32    + 
      ((11/32 : ℚ) : ℝ) * cotangentTermV 29 32    + 
      ((18/32 : ℚ) : ℝ) * cotangentTermV 30 32    + 
      ((25/32 : ℚ) : ℝ) * cotangentTermV 31 32 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_32]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((7/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((14/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((21/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((28/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((3/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((10/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((17/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((24/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((31/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((6/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((13/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((20/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((27/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((2/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((9/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((16/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((23/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((30/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((5/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((12/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((19/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((26/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((1/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((8/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((15/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((22/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((29/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((4/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((11/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((18/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((25/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31]
  try ring

def cotangentSumVFormula_39_32_lower : ℚ := -1024167076237872864927 / 219902325555200000000
def cotangentSumVFormula_39_32_upper : ℚ := -1024167071839767760073 / 219902325555200000000
theorem cotangentSumVFormula_39_32_bounds :
  ((cotangentSumVFormula_39_32_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 32 ∧
  cotangentSumVFormula 39 32 ≤ ((cotangentSumVFormula_39_32_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_32_unfold]
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
  rw [cotangentSumVFormula_39_32_lower, cotangentSumVFormula_39_32_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3239_formula_bound :
  (((8860390128994586219 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 32 39) ∧
  (vasyuninBEntryFormula 32 39 ≤ ((17721906157896561937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 32 39 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log32 := prim_log_32_bounds
  have b_log39 := prim_log_39_bounds
  have b_Vhk := cotangentSumVFormula_32_39_bounds
  have b_Vkh := cotangentSumVFormula_39_32_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_32_lower, prim_log_32_upper] at b_log32
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [cotangentSumVFormula_32_39_lower, cotangentSumVFormula_32_39_upper] at b_Vhk
  simp only [cotangentSumVFormula_39_32_lower, cotangentSumVFormula_39_32_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
