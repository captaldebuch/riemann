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

theorem cotangentSumVFormula_19_46_unfold :
    cotangentSumVFormula 19 46 =
      ((19/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 19 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_19_46_lower : ℚ := -2443735585581874041957 / 3518437208883200000000
def cotangentSumVFormula_19_46_upper : ℚ := -2443735515210288458043 / 3518437208883200000000
theorem cotangentSumVFormula_19_46_bounds :
  ((cotangentSumVFormula_19_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 46 ∧
  cotangentSumVFormula 19 46 ≤ ((cotangentSumVFormula_19_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_46_unfold]
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
  rw [cotangentSumVFormula_19_46_lower, cotangentSumVFormula_19_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_19_unfold :
    cotangentSumVFormula 46 19 =
      ((8/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_46_19_lower : ℚ := 574043569585918252459 / 1759218604441600000000
def cotangentSumVFormula_46_19_upper : ℚ := 574043604770448935041 / 1759218604441600000000
theorem cotangentSumVFormula_46_19_bounds :
  ((cotangentSumVFormula_46_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 19 ∧
  cotangentSumVFormula 46 19 ≤ ((cotangentSumVFormula_46_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_19_unfold]
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
  rw [cotangentSumVFormula_46_19_lower, cotangentSumVFormula_46_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1946_formula_bound :
  (((76294088631605830377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 46) ∧
  (vasyuninBEntryFormula 19 46 ≤ ((76298592231237075873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_19_46_bounds
  have b_Vkh := cotangentSumVFormula_46_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_19_46_lower, cotangentSumVFormula_19_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_19_lower, cotangentSumVFormula_46_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_21_46_unfold :
    cotangentSumVFormula 21 46 =
      ((21/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 21 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_21_46_lower : ℚ := 3260580163669482368417 / 879609302220800000000
def cotangentSumVFormula_21_46_upper : ℚ := 3260580181262344194083 / 879609302220800000000
theorem cotangentSumVFormula_21_46_bounds :
  ((cotangentSumVFormula_21_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 21 46 ∧
  cotangentSumVFormula 21 46 ≤ ((cotangentSumVFormula_21_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_21_46_unfold]
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
  rw [cotangentSumVFormula_21_46_lower, cotangentSumVFormula_21_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_21_unfold :
    cotangentSumVFormula 46 21 =
      ((4/21 : ℚ) : ℝ) * cotangentTermV 1 21    + 
      ((8/21 : ℚ) : ℝ) * cotangentTermV 2 21    + 
      ((12/21 : ℚ) : ℝ) * cotangentTermV 3 21    + 
      ((16/21 : ℚ) : ℝ) * cotangentTermV 4 21    + 
      ((20/21 : ℚ) : ℝ) * cotangentTermV 5 21    + 
      ((3/21 : ℚ) : ℝ) * cotangentTermV 6 21    + 
      ((7/21 : ℚ) : ℝ) * cotangentTermV 7 21    + 
      ((11/21 : ℚ) : ℝ) * cotangentTermV 8 21    + 
      ((15/21 : ℚ) : ℝ) * cotangentTermV 9 21    + 
      ((19/21 : ℚ) : ℝ) * cotangentTermV 10 21    + 
      ((2/21 : ℚ) : ℝ) * cotangentTermV 11 21    + 
      ((6/21 : ℚ) : ℝ) * cotangentTermV 12 21    + 
      ((10/21 : ℚ) : ℝ) * cotangentTermV 13 21    + 
      ((14/21 : ℚ) : ℝ) * cotangentTermV 14 21    + 
      ((18/21 : ℚ) : ℝ) * cotangentTermV 15 21    + 
      ((1/21 : ℚ) : ℝ) * cotangentTermV 16 21    + 
      ((5/21 : ℚ) : ℝ) * cotangentTermV 17 21    + 
      ((9/21 : ℚ) : ℝ) * cotangentTermV 18 21    + 
      ((13/21 : ℚ) : ℝ) * cotangentTermV 19 21    + 
      ((17/21 : ℚ) : ℝ) * cotangentTermV 20 21 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_21]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((4/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((8/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((12/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((16/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((20/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((3/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((7/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((11/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((15/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((19/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((2/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((6/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((10/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((14/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((18/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((1/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((5/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((9/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((13/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((17/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20]
  try ring

def cotangentSumVFormula_46_21_lower : ℚ := -3011662965350723100333 / 879609302220800000000
def cotangentSumVFormula_46_21_upper : ℚ := -3011662947758430805917 / 879609302220800000000
theorem cotangentSumVFormula_46_21_bounds :
  ((cotangentSumVFormula_46_21_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 21 ∧
  cotangentSumVFormula 46 21 ≤ ((cotangentSumVFormula_46_21_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_21_unfold]
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
  rw [cotangentSumVFormula_46_21_lower, cotangentSumVFormula_46_21_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2146_formula_bound :
  (((37279630348028954251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 21 46) ∧
  (vasyuninBEntryFormula 21 46 ≤ ((37281882147844389499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 21 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log21 := prim_log_21_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_21_46_bounds
  have b_Vkh := cotangentSumVFormula_46_21_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_21_lower, prim_log_21_upper] at b_log21
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_21_46_lower, cotangentSumVFormula_21_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_21_lower, cotangentSumVFormula_46_21_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_25_46_unfold :
    cotangentSumVFormula 25 46 =
      ((25/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 25 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_25_46_lower : ℚ := -3260580181262268412833 / 879609302220800000000
def cotangentSumVFormula_25_46_upper : ℚ := -3260580163669381587167 / 879609302220800000000
theorem cotangentSumVFormula_25_46_bounds :
  ((cotangentSumVFormula_25_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 46 ∧
  cotangentSumVFormula 25 46 ≤ ((cotangentSumVFormula_25_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_46_unfold]
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
  rw [cotangentSumVFormula_25_46_lower, cotangentSumVFormula_25_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_25_unfold :
    cotangentSumVFormula 46 25 =
      ((21/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((17/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((22/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((14/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((19/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((11/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((24/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((12/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_46_25_lower : ℚ := 2339075400493681223271 / 439804651110400000000
def cotangentSumVFormula_46_25_upper : ℚ := 2339075409289844557979 / 439804651110400000000
theorem cotangentSumVFormula_46_25_bounds :
  ((cotangentSumVFormula_46_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 25 ∧
  cotangentSumVFormula 46 25 ≤ ((cotangentSumVFormula_46_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_25_unfold]
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
  rw [cotangentSumVFormula_46_25_lower, cotangentSumVFormula_46_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2546_formula_bound :
  (((70135359160722017877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 46) ∧
  (vasyuninBEntryFormula 25 46 ≤ ((70139862760352513373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_25_46_bounds
  have b_Vkh := cotangentSumVFormula_46_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_25_46_lower, cotangentSumVFormula_25_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_25_lower, cotangentSumVFormula_46_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_27_46_unfold :
    cotangentSumVFormula 27 46 =
      ((27/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 27 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_27_46_lower : ℚ := 2443735515210723614293 / 3518437208883200000000
def cotangentSumVFormula_27_46_upper : ℚ := 2443735585582220135707 / 3518437208883200000000
theorem cotangentSumVFormula_27_46_bounds :
  ((cotangentSumVFormula_27_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 27 46 ∧
  cotangentSumVFormula 27 46 ≤ ((cotangentSumVFormula_27_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_27_46_unfold]
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
  rw [cotangentSumVFormula_27_46_lower, cotangentSumVFormula_27_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_27_unfold :
    cotangentSumVFormula 46 27 =
      ((19/27 : ℚ) : ℝ) * cotangentTermV 1 27    + 
      ((11/27 : ℚ) : ℝ) * cotangentTermV 2 27    + 
      ((3/27 : ℚ) : ℝ) * cotangentTermV 3 27    + 
      ((22/27 : ℚ) : ℝ) * cotangentTermV 4 27    + 
      ((14/27 : ℚ) : ℝ) * cotangentTermV 5 27    + 
      ((6/27 : ℚ) : ℝ) * cotangentTermV 6 27    + 
      ((25/27 : ℚ) : ℝ) * cotangentTermV 7 27    + 
      ((17/27 : ℚ) : ℝ) * cotangentTermV 8 27    + 
      ((9/27 : ℚ) : ℝ) * cotangentTermV 9 27    + 
      ((1/27 : ℚ) : ℝ) * cotangentTermV 10 27    + 
      ((20/27 : ℚ) : ℝ) * cotangentTermV 11 27    + 
      ((12/27 : ℚ) : ℝ) * cotangentTermV 12 27    + 
      ((4/27 : ℚ) : ℝ) * cotangentTermV 13 27    + 
      ((23/27 : ℚ) : ℝ) * cotangentTermV 14 27    + 
      ((15/27 : ℚ) : ℝ) * cotangentTermV 15 27    + 
      ((7/27 : ℚ) : ℝ) * cotangentTermV 16 27    + 
      ((26/27 : ℚ) : ℝ) * cotangentTermV 17 27    + 
      ((18/27 : ℚ) : ℝ) * cotangentTermV 18 27    + 
      ((10/27 : ℚ) : ℝ) * cotangentTermV 19 27    + 
      ((2/27 : ℚ) : ℝ) * cotangentTermV 20 27    + 
      ((21/27 : ℚ) : ℝ) * cotangentTermV 21 27    + 
      ((13/27 : ℚ) : ℝ) * cotangentTermV 22 27    + 
      ((5/27 : ℚ) : ℝ) * cotangentTermV 23 27    + 
      ((24/27 : ℚ) : ℝ) * cotangentTermV 24 27    + 
      ((16/27 : ℚ) : ℝ) * cotangentTermV 25 27    + 
      ((8/27 : ℚ) : ℝ) * cotangentTermV 26 27 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_27]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((19/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((11/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((3/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((22/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((14/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((6/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((25/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((17/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((9/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((1/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((20/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((12/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((4/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((23/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((15/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((7/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((26/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((18/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((10/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((2/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((21/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((13/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((5/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((24/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((16/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((8/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26]
  try ring

def cotangentSumVFormula_46_27_lower : ℚ := 1498533765002607368417 / 879609302220800000000
def cotangentSumVFormula_46_27_upper : ℚ := 1498533782594983256583 / 879609302220800000000
theorem cotangentSumVFormula_46_27_bounds :
  ((cotangentSumVFormula_46_27_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 27 ∧
  cotangentSumVFormula 46 27 ≤ ((cotangentSumVFormula_46_27_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_27_unfold]
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
  rw [cotangentSumVFormula_46_27_lower, cotangentSumVFormula_46_27_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2746_formula_bound :
  (((134833104851236395129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 27 46) ∧
  (vasyuninBEntryFormula 27 46 ≤ ((134842112050497229871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 27 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log27 := prim_log_27_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_27_46_bounds
  have b_Vkh := cotangentSumVFormula_46_27_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_27_lower, prim_log_27_upper] at b_log27
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_27_46_lower, cotangentSumVFormula_27_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_27_lower, cotangentSumVFormula_46_27_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_46_unfold :
    cotangentSumVFormula 29 46 =
      ((29/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 29 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_29_46_lower : ℚ := 2360771250210122993417 / 879609302220800000000
def cotangentSumVFormula_29_46_upper : ℚ := 2360771267802950444083 / 879609302220800000000
theorem cotangentSumVFormula_29_46_bounds :
  ((cotangentSumVFormula_29_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 46 ∧
  cotangentSumVFormula 29 46 ≤ ((cotangentSumVFormula_29_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_46_unfold]
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
  rw [cotangentSumVFormula_29_46_lower, cotangentSumVFormula_29_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_29_unfold :
    cotangentSumVFormula 46 29 =
      ((17/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_46_29_lower : ℚ := 789029638828384551793 / 3518437208883200000000
def cotangentSumVFormula_46_29_upper : ℚ := 789029709197999823207 / 3518437208883200000000
theorem cotangentSumVFormula_46_29_bounds :
  ((cotangentSumVFormula_46_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 29 ∧
  cotangentSumVFormula 46 29 ≤ ((cotangentSumVFormula_46_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_29_unfold]
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
  rw [cotangentSumVFormula_46_29_lower, cotangentSumVFormula_46_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2946_formula_bound :
  (((16366876353592438063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 46) ∧
  (vasyuninBEntryFormula 29 46 ≤ ((32736004506999951999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_29_46_bounds
  have b_Vkh := cotangentSumVFormula_46_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_29_46_lower, cotangentSumVFormula_29_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_29_lower, cotangentSumVFormula_46_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_46_unfold :
    cotangentSumVFormula 31 46 =
      ((31/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 31 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_31_46_lower : ℚ := -952729111796089271177 / 219902325555200000000
def cotangentSumVFormula_31_46_upper : ℚ := -59545569212367687153 / 13743895347200000000
theorem cotangentSumVFormula_31_46_bounds :
  ((cotangentSumVFormula_31_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 46 ∧
  cotangentSumVFormula 31 46 ≤ ((cotangentSumVFormula_31_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_46_unfold]
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
  rw [cotangentSumVFormula_31_46_lower, cotangentSumVFormula_31_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_31_unfold :
    cotangentSumVFormula 46 31 =
      ((15/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_46_31_lower : ℚ := 3284326363092427317021 / 439804651110400000000
def cotangentSumVFormula_46_31_upper : ℚ := 3284326371888670339229 / 439804651110400000000
theorem cotangentSumVFormula_46_31_bounds :
  ((cotangentSumVFormula_46_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 31 ∧
  cotangentSumVFormula 46 31 ≤ ((cotangentSumVFormula_46_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_31_unfold]
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
  rw [cotangentSumVFormula_46_31_lower, cotangentSumVFormula_46_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3146_formula_bound :
  (((64189554856980236627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 46) ∧
  (vasyuninBEntryFormula 31 46 ≤ ((64194058456610450873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_31_46_bounds
  have b_Vkh := cotangentSumVFormula_46_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_31_46_lower, cotangentSumVFormula_31_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_31_lower, cotangentSumVFormula_46_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_33_46_unfold :
    cotangentSumVFormula 33 46 =
      ((33/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 33 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_33_46_lower : ℚ := 2346990576188101899667 / 879609302220800000000
def cotangentSumVFormula_33_46_upper : ℚ := 2346990593780910600333 / 879609302220800000000
theorem cotangentSumVFormula_33_46_bounds :
  ((cotangentSumVFormula_33_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 46 ∧
  cotangentSumVFormula 33 46 ≤ ((cotangentSumVFormula_33_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_46_unfold]
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
  rw [cotangentSumVFormula_33_46_lower, cotangentSumVFormula_33_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_33_unfold :
    cotangentSumVFormula 46 33 =
      ((13/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((5/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((17/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((10/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((16/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((2/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((14/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((7/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_46_33_lower : ℚ := 3035387585534023614293 / 3518437208883200000000
def cotangentSumVFormula_46_33_upper : ℚ := 3035387655903826385707 / 3518437208883200000000
theorem cotangentSumVFormula_46_33_bounds :
  ((cotangentSumVFormula_46_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 33 ∧
  cotangentSumVFormula 46 33 ≤ ((cotangentSumVFormula_46_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_33_unfold]
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
  rw [cotangentSumVFormula_46_33_lower, cotangentSumVFormula_46_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3346_formula_bound :
  (((62435330094687736627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 46) ∧
  (vasyuninBEntryFormula 33 46 ≤ ((31219916847158826999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_33_46_bounds
  have b_Vkh := cotangentSumVFormula_46_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_33_46_lower, cotangentSumVFormula_33_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_33_lower, cotangentSumVFormula_46_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_35_46_unfold :
    cotangentSumVFormula 35 46 =
      ((35/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 35 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_35_46_lower : ℚ := 1674014406513559348271 / 439804651110400000000
def cotangentSumVFormula_35_46_upper : ℚ := 418503603827487018401 / 109951162777600000000
theorem cotangentSumVFormula_35_46_bounds :
  ((cotangentSumVFormula_35_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 46 ∧
  cotangentSumVFormula 35 46 ≤ ((cotangentSumVFormula_35_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_46_unfold]
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
  rw [cotangentSumVFormula_35_46_lower, cotangentSumVFormula_35_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_35_unfold :
    cotangentSumVFormula 46 35 =
      ((11/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_46_35_lower : ℚ := -1189676344364578943289 / 7036874417766400000000
def cotangentSumVFormula_46_35_upper : ℚ := -1189676203624046056711 / 7036874417766400000000
theorem cotangentSumVFormula_46_35_bounds :
  ((cotangentSumVFormula_46_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 35 ∧
  cotangentSumVFormula 46 35 ≤ ((cotangentSumVFormula_46_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_35_unfold]
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
  rw [cotangentSumVFormula_46_35_lower, cotangentSumVFormula_46_35_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3546_formula_bound :
  (((30657174214790423001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 35 46) ∧
  (vasyuninBEntryFormula 35 46 ≤ ((61318852029210825873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 35 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log35 := prim_log_35_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_35_46_bounds
  have b_Vkh := cotangentSumVFormula_46_35_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_35_46_lower, cotangentSumVFormula_35_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_35_lower, cotangentSumVFormula_46_35_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_46_unfold :
    cotangentSumVFormula 37 46 =
      ((37/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 37 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_37_46_lower : ℚ := 1168846133941064635073 / 219902325555200000000
def cotangentSumVFormula_37_46_upper : ℚ := 584423069169626862151 / 109951162777600000000
theorem cotangentSumVFormula_37_46_bounds :
  ((cotangentSumVFormula_37_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 46 ∧
  cotangentSumVFormula 37 46 ≤ ((cotangentSumVFormula_37_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_46_unfold]
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
  rw [cotangentSumVFormula_37_46_lower, cotangentSumVFormula_37_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_37_unfold :
    cotangentSumVFormula 46 37 =
      ((9/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 46 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_46_37_lower : ℚ := -2986691804981180185041 / 1759218604441600000000
def cotangentSumVFormula_46_37_upper : ℚ := -2986691769796032314959 / 1759218604441600000000
theorem cotangentSumVFormula_46_37_bounds :
  ((cotangentSumVFormula_46_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 37 ∧
  cotangentSumVFormula 46 37 ≤ ((cotangentSumVFormula_46_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_37_unfold]
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
  rw [cotangentSumVFormula_46_37_lower, cotangentSumVFormula_46_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3746_formula_bound :
  (((60401079419131111627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 46) ∧
  (vasyuninBEntryFormula 37 46 ≤ ((30202791509380451999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_37_46_bounds
  have b_Vkh := cotangentSumVFormula_46_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_37_46_lower, cotangentSumVFormula_37_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_37_lower, cotangentSumVFormula_46_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_39_46_unfold :
    cotangentSumVFormula 39 46 =
      ((39/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 39 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_39_46_lower : ℚ := 2449037218729164635073 / 219902325555200000000
def cotangentSumVFormula_39_46_upper : ℚ := 2449037223127341614927 / 219902325555200000000
theorem cotangentSumVFormula_39_46_bounds :
  ((cotangentSumVFormula_39_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 46 ∧
  cotangentSumVFormula 39 46 ≤ ((cotangentSumVFormula_39_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_46_unfold]
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
  rw [cotangentSumVFormula_39_46_lower, cotangentSumVFormula_39_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_39_unfold :
    cotangentSumVFormula 46 39 =
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
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 46 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_46_39_lower : ℚ := -1692605911470720521177 / 219902325555200000000
def cotangentSumVFormula_46_39_upper : ℚ := -846302953536277044099 / 109951162777600000000
theorem cotangentSumVFormula_46_39_bounds :
  ((cotangentSumVFormula_46_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 39 ∧
  cotangentSumVFormula 46 39 ≤ ((cotangentSumVFormula_46_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_39_unfold]
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
  rw [cotangentSumVFormula_46_39_lower, cotangentSumVFormula_46_39_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3946_formula_bound :
  (((119481528798054176379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 39 46) ∧
  (vasyuninBEntryFormula 39 46 ≤ ((119490535997313667371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 39 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log39 := prim_log_39_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_39_46_bounds
  have b_Vkh := cotangentSumVFormula_46_39_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_39_46_lower, cotangentSumVFormula_39_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_39_lower, cotangentSumVFormula_46_39_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_46_unfold :
    cotangentSumVFormula 41 46 =
      ((41/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 41 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_41_46_lower : ℚ := 1620047347943923137849 / 109951162777600000000
def cotangentSumVFormula_41_46_upper : ℚ := 1620047350143008893401 / 109951162777600000000
theorem cotangentSumVFormula_41_46_bounds :
  ((cotangentSumVFormula_41_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 46 ∧
  cotangentSumVFormula 41 46 ≤ ((cotangentSumVFormula_41_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_46_unfold]
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
  rw [cotangentSumVFormula_41_46_lower, cotangentSumVFormula_41_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_41_unfold :
    cotangentSumVFormula 46 41 =
      ((5/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((4/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((9/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((3/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((8/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((2/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((1/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((6/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 46 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_46_41_lower : ℚ := -2574355997069143177427 / 219902325555200000000
def cotangentSumVFormula_46_41_upper : ℚ := -2574355992670983385073 / 219902325555200000000
theorem cotangentSumVFormula_46_41_bounds :
  ((cotangentSumVFormula_46_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 41 ∧
  cotangentSumVFormula 46 41 ≤ ((cotangentSumVFormula_46_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_41_unfold]
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
  rw [cotangentSumVFormula_46_41_lower, cotangentSumVFormula_46_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4146_formula_bound :
  (((118902998871342395129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 46) ∧
  (vasyuninBEntryFormula 41 46 ≤ ((118912006070601511121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_41_46_bounds
  have b_Vkh := cotangentSumVFormula_46_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_41_46_lower, cotangentSumVFormula_41_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_41_lower, cotangentSumVFormula_46_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_43_46_unfold :
    cotangentSumVFormula 43 46 =
      ((43/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((45/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 43 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_43_46_lower : ℚ := 2449081309953772356599 / 109951162777600000000
def cotangentSumVFormula_43_46_upper : ℚ := 2449081312152872955901 / 109951162777600000000
theorem cotangentSumVFormula_43_46_bounds :
  ((cotangentSumVFormula_43_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 46 ∧
  cotangentSumVFormula 43 46 ≤ ((cotangentSumVFormula_43_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_46_unfold]
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
  rw [cotangentSumVFormula_43_46_lower, cotangentSumVFormula_43_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_43_unfold :
    cotangentSumVFormula 46 43 =
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
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 46 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_46_43_lower : ℚ := -548321608165038453819 / 27487790694400000000
def cotangentSumVFormula_46_43_upper : ℚ := -1096643215230520357987 / 54975581388800000000
theorem cotangentSumVFormula_46_43_bounds :
  ((cotangentSumVFormula_46_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 43 ∧
  cotangentSumVFormula 46 43 ≤ ((cotangentSumVFormula_46_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_43_unfold]
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
  rw [cotangentSumVFormula_46_43_lower, cotangentSumVFormula_46_43_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4346_formula_bound :
  (((119174462041384457629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 43 46) ∧
  (vasyuninBEntryFormula 43 46 ≤ ((119183469240644917371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 43 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log43 := log_43_certified_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_43_46_bounds
  have b_Vkh := cotangentSumVFormula_46_43_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_43_46_lower, cotangentSumVFormula_43_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_43_lower, cotangentSumVFormula_46_43_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_45_46_unfold :
    cotangentSumVFormula 45 46 =
      ((45/46 : ℚ) : ℝ) * cotangentTermV 1 46    + 
      ((44/46 : ℚ) : ℝ) * cotangentTermV 2 46    + 
      ((43/46 : ℚ) : ℝ) * cotangentTermV 3 46    + 
      ((42/46 : ℚ) : ℝ) * cotangentTermV 4 46    + 
      ((41/46 : ℚ) : ℝ) * cotangentTermV 5 46    + 
      ((40/46 : ℚ) : ℝ) * cotangentTermV 6 46    + 
      ((39/46 : ℚ) : ℝ) * cotangentTermV 7 46    + 
      ((38/46 : ℚ) : ℝ) * cotangentTermV 8 46    + 
      ((37/46 : ℚ) : ℝ) * cotangentTermV 9 46    + 
      ((36/46 : ℚ) : ℝ) * cotangentTermV 10 46    + 
      ((35/46 : ℚ) : ℝ) * cotangentTermV 11 46    + 
      ((34/46 : ℚ) : ℝ) * cotangentTermV 12 46    + 
      ((33/46 : ℚ) : ℝ) * cotangentTermV 13 46    + 
      ((32/46 : ℚ) : ℝ) * cotangentTermV 14 46    + 
      ((31/46 : ℚ) : ℝ) * cotangentTermV 15 46    + 
      ((30/46 : ℚ) : ℝ) * cotangentTermV 16 46    + 
      ((29/46 : ℚ) : ℝ) * cotangentTermV 17 46    + 
      ((28/46 : ℚ) : ℝ) * cotangentTermV 18 46    + 
      ((27/46 : ℚ) : ℝ) * cotangentTermV 19 46    + 
      ((26/46 : ℚ) : ℝ) * cotangentTermV 20 46    + 
      ((25/46 : ℚ) : ℝ) * cotangentTermV 21 46    + 
      ((24/46 : ℚ) : ℝ) * cotangentTermV 22 46    + 
      ((23/46 : ℚ) : ℝ) * cotangentTermV 23 46    + 
      ((22/46 : ℚ) : ℝ) * cotangentTermV 24 46    + 
      ((21/46 : ℚ) : ℝ) * cotangentTermV 25 46    + 
      ((20/46 : ℚ) : ℝ) * cotangentTermV 26 46    + 
      ((19/46 : ℚ) : ℝ) * cotangentTermV 27 46    + 
      ((18/46 : ℚ) : ℝ) * cotangentTermV 28 46    + 
      ((17/46 : ℚ) : ℝ) * cotangentTermV 29 46    + 
      ((16/46 : ℚ) : ℝ) * cotangentTermV 30 46    + 
      ((15/46 : ℚ) : ℝ) * cotangentTermV 31 46    + 
      ((14/46 : ℚ) : ℝ) * cotangentTermV 32 46    + 
      ((13/46 : ℚ) : ℝ) * cotangentTermV 33 46    + 
      ((12/46 : ℚ) : ℝ) * cotangentTermV 34 46    + 
      ((11/46 : ℚ) : ℝ) * cotangentTermV 35 46    + 
      ((10/46 : ℚ) : ℝ) * cotangentTermV 36 46    + 
      ((9/46 : ℚ) : ℝ) * cotangentTermV 37 46    + 
      ((8/46 : ℚ) : ℝ) * cotangentTermV 38 46    + 
      ((7/46 : ℚ) : ℝ) * cotangentTermV 39 46    + 
      ((6/46 : ℚ) : ℝ) * cotangentTermV 40 46    + 
      ((5/46 : ℚ) : ℝ) * cotangentTermV 41 46    + 
      ((4/46 : ℚ) : ℝ) * cotangentTermV 42 46    + 
      ((3/46 : ℚ) : ℝ) * cotangentTermV 43 46    + 
      ((2/46 : ℚ) : ℝ) * cotangentTermV 44 46    + 
      ((1/46 : ℚ) : ℝ) * cotangentTermV 45 46 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_46]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 45 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_45_46_lower : ℚ := 2084741349060886764237 / 54975581388800000000
def cotangentSumVFormula_45_46_upper : ℚ := 2084741350160438235763 / 54975581388800000000
theorem cotangentSumVFormula_45_46_bounds :
  ((cotangentSumVFormula_45_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 46 ∧
  cotangentSumVFormula 45 46 ≤ ((cotangentSumVFormula_45_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_46_unfold]
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
  rw [cotangentSumVFormula_45_46_lower, cotangentSumVFormula_45_46_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_46_45_unfold :
    cotangentSumVFormula 46 45 =
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
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 46 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_46_45_lower : ℚ := -2022498221511643704513 / 54975581388800000000
def cotangentSumVFormula_46_45_upper : ℚ := -2022498220412081295487 / 54975581388800000000
theorem cotangentSumVFormula_46_45_bounds :
  ((cotangentSumVFormula_46_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 45 ∧
  cotangentSumVFormula 46 45 ≤ ((cotangentSumVFormula_46_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_45_unfold]
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
  rw [cotangentSumVFormula_46_45_lower, cotangentSumVFormula_46_45_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4546_formula_bound :
  (((30224475759841423001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 45 46) ∧
  (vasyuninBEntryFormula 45 46 ≤ ((30226727559656576999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 45 46 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log45 := prim_log_45_bounds
  have b_log46 := prim_log_46_bounds
  have b_Vhk := cotangentSumVFormula_45_46_bounds
  have b_Vkh := cotangentSumVFormula_46_45_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [cotangentSumVFormula_45_46_lower, cotangentSumVFormula_45_46_upper] at b_Vhk
  simp only [cotangentSumVFormula_46_45_lower, cotangentSumVFormula_46_45_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_47_unfold :
    cotangentSumVFormula 1 47 =
      ((1/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 1 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_1_47_lower : ℚ := -1073682513159667360069 / 27487790694400000000
def cotangentSumVFormula_1_47_upper : ℚ := -536841256304941905903 / 13743895347200000000
theorem cotangentSumVFormula_1_47_bounds :
  ((cotangentSumVFormula_1_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 47 ∧
  cotangentSumVFormula 1 47 ≤ ((cotangentSumVFormula_1_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_47_unfold]
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
  rw [cotangentSumVFormula_1_47_lower, cotangentSumVFormula_1_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_1_unfold :
    cotangentSumVFormula 47 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_47_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_47_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_47_1_bounds :
  ((cotangentSumVFormula_47_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 1 ∧
  cotangentSumVFormula 47 1 ≤ ((cotangentSumVFormula_47_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_1_unfold]
  rw [cotangentSumVFormula_47_1_lower, cotangentSumVFormula_47_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_147_formula_bound :
  (((73261922803161266751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 47) ∧
  (vasyuninBEntryFormula 1 47 ≤ ((73264174603017733249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_47_bounds
  have b_Vkh := cotangentSumVFormula_47_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_1_47_lower, cotangentSumVFormula_1_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_1_lower, cotangentSumVFormula_47_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_47_unfold :
    cotangentSumVFormula 2 47 =
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
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 2 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_2_47_lower : ℚ := -3189242832529579205901 / 109951162777600000000
def cotangentSumVFormula_2_47_upper : ℚ := -3189242830330444231599 / 109951162777600000000
theorem cotangentSumVFormula_2_47_bounds :
  ((cotangentSumVFormula_2_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 47 ∧
  cotangentSumVFormula 2 47 ≤ ((cotangentSumVFormula_2_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_47_unfold]
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
  rw [cotangentSumVFormula_2_47_lower, cotangentSumVFormula_2_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_2_unfold :
    cotangentSumVFormula 47 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_47_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_47_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_47_2_bounds :
  ((cotangentSumVFormula_47_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 2 ∧
  cotangentSumVFormula 47 2 ≤ ((cotangentSumVFormula_47_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_47_2_lower, cotangentSumVFormula_47_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_247_formula_bound :
  (((32436161808746281813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 47) ∧
  (vasyuninBEntryFormula 2 47 ≤ ((32437287708663655687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_47_bounds
  have b_Vkh := cotangentSumVFormula_47_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_2_47_lower, cotangentSumVFormula_2_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_2_lower, cotangentSumVFormula_47_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_47_unfold :
    cotangentSumVFormula 3 47 =
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
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 3 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_3_47_lower : ℚ := -2578191821266652643401 / 109951162777600000000
def cotangentSumVFormula_3_47_upper : ℚ := -2578191819067520012849 / 109951162777600000000
theorem cotangentSumVFormula_3_47_bounds :
  ((cotangentSumVFormula_3_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 47 ∧
  cotangentSumVFormula 3 47 ≤ ((cotangentSumVFormula_3_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_47_unfold]
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
  rw [cotangentSumVFormula_3_47_lower, cotangentSumVFormula_3_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_3_unfold :
    cotangentSumVFormula 47 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_47_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_47_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_47_3_bounds :
  ((cotangentSumVFormula_47_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 3 ∧
  cotangentSumVFormula 47 3 ≤ ((cotangentSumVFormula_47_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_47_3_lower, cotangentSumVFormula_47_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_347_formula_bound :
  (((119986805069855424127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 47) ∧
  (vasyuninBEntryFormula 3 47 ≤ ((119991308669510450873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_47_bounds
  have b_Vkh := cotangentSumVFormula_47_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_3_47_lower, cotangentSumVFormula_3_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_3_lower, cotangentSumVFormula_47_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_47_unfold :
    cotangentSumVFormula 4 47 =
      ((4/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 4 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_4_47_lower : ℚ := -2173699103757915143401 / 109951162777600000000
def cotangentSumVFormula_4_47_upper : ℚ := -2173699101558785637849 / 109951162777600000000
theorem cotangentSumVFormula_4_47_bounds :
  ((cotangentSumVFormula_4_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 47 ∧
  cotangentSumVFormula 4 47 ≤ ((cotangentSumVFormula_4_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_47_unfold]
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
  rw [cotangentSumVFormula_4_47_lower, cotangentSumVFormula_4_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_4_unfold :
    cotangentSumVFormula 47 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_47_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_47_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_47_4_bounds :
  ((cotangentSumVFormula_47_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 4 ∧
  cotangentSumVFormula 47 4 ≤ ((cotangentSumVFormula_47_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_47_4_lower, cotangentSumVFormula_47_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_447_formula_bound :
  (((56549956307556235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 47) ∧
  (vasyuninBEntryFormula 4 47 ≤ ((56552208107379889499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_47_bounds
  have b_Vkh := cotangentSumVFormula_47_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_4_47_lower, cotangentSumVFormula_4_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_4_lower, cotangentSumVFormula_47_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_47_unfold :
    cotangentSumVFormula 5 47 =
      ((5/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 5 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_5_47_lower : ℚ := -888499798982465579513 / 54975581388800000000
def cotangentSumVFormula_5_47_upper : ℚ := -444249898941449827431 / 27487790694400000000
theorem cotangentSumVFormula_5_47_bounds :
  ((cotangentSumVFormula_5_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 47 ∧
  cotangentSumVFormula 5 47 ≤ ((cotangentSumVFormula_5_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_47_unfold]
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
  rw [cotangentSumVFormula_5_47_lower, cotangentSumVFormula_5_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_5_unfold :
    cotangentSumVFormula 47 5 =
      ((2/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_47_5_lower : ℚ := -2260935825867423195031 / 28147497671065600000000
def cotangentSumVFormula_47_5_upper : ℚ := -2260935262917351804969 / 28147497671065600000000
theorem cotangentSumVFormula_47_5_bounds :
  ((cotangentSumVFormula_47_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 5 ∧
  cotangentSumVFormula 47 5 ≤ ((cotangentSumVFormula_47_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_47_5_lower, cotangentSumVFormula_47_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_547_formula_bound :
  (((107655171254010830377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 47) ∧
  (vasyuninBEntryFormula 5 47 ≤ ((107659674853654482123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_47_bounds
  have b_Vkh := cotangentSumVFormula_47_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_5_47_lower, cotangentSumVFormula_5_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_5_lower, cotangentSumVFormula_47_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_47_unfold :
    cotangentSumVFormula 6 47 =
      ((6/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 6 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_6_47_lower : ℚ := -1670371340573637018401 / 109951162777600000000
def cotangentSumVFormula_6_47_upper : ℚ := -1670371338374505950349 / 109951162777600000000
theorem cotangentSumVFormula_6_47_bounds :
  ((cotangentSumVFormula_6_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 47 ∧
  cotangentSumVFormula 6 47 ≤ ((cotangentSumVFormula_6_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_47_unfold]
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
  rw [cotangentSumVFormula_6_47_lower, cotangentSumVFormula_6_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_6_unfold :
    cotangentSumVFormula 47 6 =
      ((5/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((1/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_47_6_lower : ℚ := 148120776897660637849 / 109951162777600000000
def cotangentSumVFormula_47_6_upper : ℚ := 1184966232773477787833 / 879609302220800000000
theorem cotangentSumVFormula_47_6_bounds :
  ((cotangentSumVFormula_47_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 6 ∧
  cotangentSumVFormula 47 6 ≤ ((cotangentSumVFormula_47_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_6_unfold]
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
  rw [cotangentSumVFormula_47_6_lower, cotangentSumVFormula_47_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_647_formula_bound :
  (((103468052492833236627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 47) ∧
  (vasyuninBEntryFormula 6 47 ≤ ((103472556092474138373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_47_bounds
  have b_Vkh := cotangentSumVFormula_47_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_6_47_lower, cotangentSumVFormula_6_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_6_lower, cotangentSumVFormula_47_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_47_unfold :
    cotangentSumVFormula 7 47 =
      ((7/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 7 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_7_47_lower : ℚ := -684514546773237454513 / 54975581388800000000
def cotangentSumVFormula_7_47_upper : ℚ := -684514545673671920487 / 54975581388800000000
theorem cotangentSumVFormula_7_47_bounds :
  ((cotangentSumVFormula_7_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 47 ∧
  cotangentSumVFormula 7 47 ≤ ((cotangentSumVFormula_7_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_47_unfold]
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
  rw [cotangentSumVFormula_7_47_lower, cotangentSumVFormula_7_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_7_unfold :
    cotangentSumVFormula 47 7 =
      ((5/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_47_7_lower : ℚ := 2156738354928926739293 / 3518437208883200000000
def cotangentSumVFormula_47_7_upper : ℚ := 2156738425297699041957 / 3518437208883200000000
theorem cotangentSumVFormula_47_7_bounds :
  ((cotangentSumVFormula_47_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 7 ∧
  cotangentSumVFormula 47 7 ≤ ((cotangentSumVFormula_47_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_7_unfold]
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
  rw [cotangentSumVFormula_47_7_lower, cotangentSumVFormula_47_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_747_formula_bound :
  (((99573925157474361627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 47) ∧
  (vasyuninBEntryFormula 7 47 ≤ ((99578428757113169623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_7_47_bounds
  have b_Vkh := cotangentSumVFormula_47_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_7_47_lower, cotangentSumVFormula_7_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_7_lower, cotangentSumVFormula_47_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_47_unfold :
    cotangentSumVFormula 8 47 =
      ((8/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 8 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_8_47_lower : ℚ := -1386037083528629987151 / 109951162777600000000
def cotangentSumVFormula_8_47_upper : ℚ := -1386037081329500481599 / 109951162777600000000
theorem cotangentSumVFormula_8_47_bounds :
  ((cotangentSumVFormula_8_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 47 ∧
  cotangentSumVFormula 8 47 ≤ ((cotangentSumVFormula_8_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_47_unfold]
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
  rw [cotangentSumVFormula_8_47_lower, cotangentSumVFormula_8_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_8_unfold :
    cotangentSumVFormula 47 8 =
      ((7/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_47_8_lower : ℚ := 2123564698214891743417 / 879609302220800000000
def cotangentSumVFormula_47_8_upper : ℚ := 2123564715807086381583 / 879609302220800000000
theorem cotangentSumVFormula_47_8_bounds :
  ((cotangentSumVFormula_47_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 8 ∧
  cotangentSumVFormula 47 8 ≤ ((cotangentSumVFormula_47_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_8_unfold]
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
  rw [cotangentSumVFormula_47_8_lower, cotangentSumVFormula_47_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_847_formula_bound :
  (((96708580382007736627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 47) ∧
  (vasyuninBEntryFormula 8 47 ≤ ((96713083981644919623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_8_47_bounds
  have b_Vkh := cotangentSumVFormula_47_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_8_47_lower, cotangentSumVFormula_8_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_8_lower, cotangentSumVFormula_47_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
