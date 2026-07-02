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

theorem cotangentSumVFormula_9_47_unfold :
    cotangentSumVFormula 9 47 =
      ((9/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 9 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_9_47_lower : ℚ := -3251228888853009401729 / 439804651110400000000
def cotangentSumVFormula_9_47_upper : ℚ := -3251228880056487473271 / 439804651110400000000
theorem cotangentSumVFormula_9_47_bounds :
  ((cotangentSumVFormula_9_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 47 ∧
  cotangentSumVFormula 9 47 ≤ ((cotangentSumVFormula_9_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_47_unfold]
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
  rw [cotangentSumVFormula_9_47_lower, cotangentSumVFormula_9_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_9_unfold :
    cotangentSumVFormula 47 9 =
      ((2/9 : ℚ) : ℝ) * cotangentTermV 1 9    + 
      ((4/9 : ℚ) : ℝ) * cotangentTermV 2 9    + 
      ((6/9 : ℚ) : ℝ) * cotangentTermV 3 9    + 
      ((8/9 : ℚ) : ℝ) * cotangentTermV 4 9    + 
      ((1/9 : ℚ) : ℝ) * cotangentTermV 5 9    + 
      ((3/9 : ℚ) : ℝ) * cotangentTermV 6 9    + 
      ((5/9 : ℚ) : ℝ) * cotangentTermV 7 9    + 
      ((7/9 : ℚ) : ℝ) * cotangentTermV 8 9 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_9]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_47_9_lower : ℚ := -1169176792736990287833 / 879609302220800000000
def cotangentSumVFormula_47_9_upper : ℚ := -1169176775144784712167 / 879609302220800000000
theorem cotangentSumVFormula_47_9_bounds :
  ((cotangentSumVFormula_47_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 9 ∧
  cotangentSumVFormula 47 9 ≤ ((cotangentSumVFormula_47_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_9_unfold]
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
  rw [cotangentSumVFormula_47_9_lower, cotangentSumVFormula_47_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_947_formula_bound :
  (((46825929192036923001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 47) ∧
  (vasyuninBEntryFormula 9 47 ≤ ((46828180991855076999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_9_47_bounds
  have b_Vkh := cotangentSumVFormula_47_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_9_47_lower, cotangentSumVFormula_9_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_9_lower, cotangentSumVFormula_47_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_47_unfold :
    cotangentSumVFormula 10 47 =
      ((10/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 10 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_10_47_lower : ℚ := -1760152483024737708677 / 219902325555200000000
def cotangentSumVFormula_10_47_upper : ℚ := -1760152478626480260073 / 219902325555200000000
theorem cotangentSumVFormula_10_47_bounds :
  ((cotangentSumVFormula_10_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 47 ∧
  cotangentSumVFormula 10 47 ≤ ((cotangentSumVFormula_10_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_47_unfold]
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
  rw [cotangentSumVFormula_10_47_lower, cotangentSumVFormula_10_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_10_unfold :
    cotangentSumVFormula 47 10 =
      ((7/10 : ℚ) : ℝ) * cotangentTermV 1 10    + 
      ((4/10 : ℚ) : ℝ) * cotangentTermV 2 10    + 
      ((1/10 : ℚ) : ℝ) * cotangentTermV 3 10    + 
      ((8/10 : ℚ) : ℝ) * cotangentTermV 4 10    + 
      ((5/10 : ℚ) : ℝ) * cotangentTermV 5 10    + 
      ((2/10 : ℚ) : ℝ) * cotangentTermV 6 10    + 
      ((9/10 : ℚ) : ℝ) * cotangentTermV 7 10    + 
      ((6/10 : ℚ) : ℝ) * cotangentTermV 8 10    + 
      ((3/10 : ℚ) : ℝ) * cotangentTermV 9 10 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_10]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_47_10_lower : ℚ := 2003802120016315801793 / 3518437208883200000000
def cotangentSumVFormula_47_10_upper : ℚ := 2003802190385117791957 / 3518437208883200000000
theorem cotangentSumVFormula_47_10_bounds :
  ((cotangentSumVFormula_47_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 10 ∧
  cotangentSumVFormula 47 10 ≤ ((cotangentSumVFormula_47_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_10_unfold]
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
  rw [cotangentSumVFormula_47_10_lower, cotangentSumVFormula_47_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1047_formula_bound :
  (((22729910672591031813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 47) ∧
  (vasyuninBEntryFormula 10 47 ≤ ((22731036572499843187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_10_47_bounds
  have b_Vkh := cotangentSumVFormula_47_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_10_47_lower, cotangentSumVFormula_10_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_10_lower, cotangentSumVFormula_47_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_47_unfold :
    cotangentSumVFormula 11 47 =
      ((11/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 11 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_11_47_lower : ℚ := -557040351283570612151 / 109951162777600000000
def cotangentSumVFormula_11_47_upper : ℚ := -278520174542221920487 / 54975581388800000000
theorem cotangentSumVFormula_11_47_bounds :
  ((cotangentSumVFormula_11_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 47 ∧
  cotangentSumVFormula 11 47 ≤ ((cotangentSumVFormula_11_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_47_unfold]
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
  rw [cotangentSumVFormula_11_47_lower, cotangentSumVFormula_11_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_11_unfold :
    cotangentSumVFormula 47 11 =
      ((3/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_47_11_lower : ℚ := -2230748134936280966291 / 1759218604441600000000
def cotangentSumVFormula_47_11_upper : ℚ := -2230748099751851064959 / 1759218604441600000000
theorem cotangentSumVFormula_47_11_bounds :
  ((cotangentSumVFormula_47_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 11 ∧
  cotangentSumVFormula 47 11 ≤ ((cotangentSumVFormula_47_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_11_unfold]
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
  rw [cotangentSumVFormula_47_11_lower, cotangentSumVFormula_47_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1147_formula_bound :
  (((44356525162524141751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 47) ∧
  (vasyuninBEntryFormula 11 47 ≤ ((44358776962341389499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_11_47_bounds
  have b_Vkh := cotangentSumVFormula_47_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_11_47_lower, cotangentSumVFormula_11_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_11_lower, cotangentSumVFormula_47_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_12_47_unfold :
    cotangentSumVFormula 12 47 =
      ((12/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 12 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_12_47_lower : ℚ := -575160481416463235763 / 54975581388800000000
def cotangentSumVFormula_12_47_upper : ℚ := -575160480316900826737 / 54975581388800000000
theorem cotangentSumVFormula_12_47_bounds :
  ((cotangentSumVFormula_12_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 47 ∧
  cotangentSumVFormula 12 47 ≤ ((cotangentSumVFormula_12_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_47_unfold]
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
  rw [cotangentSumVFormula_12_47_lower, cotangentSumVFormula_12_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_12_unfold :
    cotangentSumVFormula 47 12 =
      ((11/12 : ℚ) : ℝ) * cotangentTermV 1 12    + 
      ((10/12 : ℚ) : ℝ) * cotangentTermV 2 12    + 
      ((9/12 : ℚ) : ℝ) * cotangentTermV 3 12    + 
      ((8/12 : ℚ) : ℝ) * cotangentTermV 4 12    + 
      ((7/12 : ℚ) : ℝ) * cotangentTermV 5 12    + 
      ((6/12 : ℚ) : ℝ) * cotangentTermV 6 12    + 
      ((5/12 : ℚ) : ℝ) * cotangentTermV 7 12    + 
      ((4/12 : ℚ) : ℝ) * cotangentTermV 8 12    + 
      ((3/12 : ℚ) : ℝ) * cotangentTermV 9 12    + 
      ((2/12 : ℚ) : ℝ) * cotangentTermV 10 12    + 
      ((1/12 : ℚ) : ℝ) * cotangentTermV 11 12 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_12]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_47_12_lower : ℚ := 2199837402785514817021 / 439804651110400000000
def cotangentSumVFormula_47_12_upper : ℚ := 2199837411581621901729 / 439804651110400000000
theorem cotangentSumVFormula_47_12_bounds :
  ((cotangentSumVFormula_47_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 12 ∧
  cotangentSumVFormula 47 12 ≤ ((cotangentSumVFormula_47_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_12_unfold]
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
  rw [cotangentSumVFormula_47_12_lower, cotangentSumVFormula_47_12_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1247_formula_bound :
  (((43666914719209173001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 12 47) ∧
  (vasyuninBEntryFormula 12 47 ≤ ((21834583259513030687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 12 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log12 := prim_log_12_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_12_47_bounds
  have b_Vkh := cotangentSumVFormula_47_12_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_12_47_lower, cotangentSumVFormula_12_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_12_lower, cotangentSumVFormula_47_12_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_47_unfold :
    cotangentSumVFormula 13 47 =
      ((13/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 13 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_13_47_lower : ℚ := -2104150706002947682979 / 439804651110400000000
def cotangentSumVFormula_13_47_upper : ℚ := -2104150697206451535771 / 439804651110400000000
theorem cotangentSumVFormula_13_47_bounds :
  ((cotangentSumVFormula_13_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 47 ∧
  cotangentSumVFormula 13 47 ≤ ((cotangentSumVFormula_13_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_47_unfold]
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
  rw [cotangentSumVFormula_13_47_lower, cotangentSumVFormula_13_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_13_unfold :
    cotangentSumVFormula 47 13 =
      ((8/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_47_13_lower : ℚ := 80147675644260728823 / 219902325555200000000
def cotangentSumVFormula_47_13_upper : ℚ := 80147680042317396177 / 219902325555200000000
theorem cotangentSumVFormula_47_13_bounds :
  ((cotangentSumVFormula_47_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 13 ∧
  cotangentSumVFormula 47 13 ≤ ((cotangentSumVFormula_47_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_13_unfold]
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
  rw [cotangentSumVFormula_47_13_lower, cotangentSumVFormula_47_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1347_formula_bound :
  (((10555767976611429969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 47) ∧
  (vasyuninBEntryFormula 13 47 ≤ ((21112661853131186937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_13_47_bounds
  have b_Vkh := cotangentSumVFormula_47_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_13_47_lower, cotangentSumVFormula_13_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_13_lower, cotangentSumVFormula_47_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_14_47_unfold :
    cotangentSumVFormula 14 47 =
      ((14/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 14 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_14_47_lower : ℚ := -966319141350061745479 / 439804651110400000000
def cotangentSumVFormula_14_47_upper : ℚ := -966319132553575754521 / 439804651110400000000
theorem cotangentSumVFormula_14_47_bounds :
  ((cotangentSumVFormula_14_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 47 ∧
  cotangentSumVFormula 14 47 ≤ ((cotangentSumVFormula_14_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_47_unfold]
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
  rw [cotangentSumVFormula_14_47_lower, cotangentSumVFormula_14_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_14_unfold :
    cotangentSumVFormula 47 14 =
      ((5/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((1/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((3/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_47_14_lower : ℚ := -2530551200052683310041 / 1759218604441600000000
def cotangentSumVFormula_47_14_upper : ℚ := -2530551164868205752459 / 1759218604441600000000
theorem cotangentSumVFormula_47_14_bounds :
  ((cotangentSumVFormula_47_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 14 ∧
  cotangentSumVFormula 47 14 ≤ ((cotangentSumVFormula_47_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_14_unfold]
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
  rw [cotangentSumVFormula_47_14_lower, cotangentSumVFormula_47_14_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1447_formula_bound :
  (((41369675376056391751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 14 47) ∧
  (vasyuninBEntryFormula 14 47 ≤ ((41371927175872826999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 14 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log14 := prim_log_14_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_14_47_bounds
  have b_Vkh := cotangentSumVFormula_47_14_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_14_47_lower, cotangentSumVFormula_14_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_14_lower, cotangentSumVFormula_47_14_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_47_unfold :
    cotangentSumVFormula 15 47 =
      ((15/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 15 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_15_47_lower : ℚ := 1031373101295333930917 / 879609302220800000000
def cotangentSumVFormula_15_47_upper : ℚ := 1031373118888303569083 / 879609302220800000000
theorem cotangentSumVFormula_15_47_bounds :
  ((cotangentSumVFormula_15_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 47 ∧
  cotangentSumVFormula 15 47 ≤ ((cotangentSumVFormula_15_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_47_unfold]
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
  rw [cotangentSumVFormula_15_47_lower, cotangentSumVFormula_15_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_15_unfold :
    cotangentSumVFormula 47 15 =
      ((2/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((4/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_47_15_lower : ℚ := -1862559410021953932979 / 439804651110400000000
def cotangentSumVFormula_47_15_upper : ℚ := -1862559401225831223271 / 439804651110400000000
theorem cotangentSumVFormula_47_15_bounds :
  ((cotangentSumVFormula_47_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 15 ∧
  cotangentSumVFormula 47 15 ≤ ((cotangentSumVFormula_47_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_15_unfold]
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
  rw [cotangentSumVFormula_47_15_lower, cotangentSumVFormula_47_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1547_formula_bound :
  (((81820824995379830377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 47) ∧
  (vasyuninBEntryFormula 15 47 ≤ ((81825328595012325873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_15_47_bounds
  have b_Vkh := cotangentSumVFormula_47_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_15_47_lower, cotangentSumVFormula_15_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_15_lower, cotangentSumVFormula_47_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_16_47_unfold :
    cotangentSumVFormula 16 47 =
      ((16/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 16 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_16_47_lower : ℚ := -1161248685262780768401 / 109951162777600000000
def cotangentSumVFormula_16_47_upper : ℚ := -1161248683063659856599 / 109951162777600000000
theorem cotangentSumVFormula_16_47_bounds :
  ((cotangentSumVFormula_16_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 47 ∧
  cotangentSumVFormula 16 47 ≤ ((cotangentSumVFormula_16_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_47_unfold]
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
  rw [cotangentSumVFormula_16_47_lower, cotangentSumVFormula_16_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_16_unfold :
    cotangentSumVFormula 47 16 =
      ((15/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_47_16_lower : ℚ := 1764484219457194322573 / 219902325555200000000
def cotangentSumVFormula_47_16_upper : ℚ := 1764484223855254896177 / 219902325555200000000
theorem cotangentSumVFormula_47_16_bounds :
  ((cotangentSumVFormula_47_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 16 ∧
  cotangentSumVFormula 47 16 ≤ ((cotangentSumVFormula_47_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_16_unfold]
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
  rw [cotangentSumVFormula_47_16_lower, cotangentSumVFormula_47_16_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1647_formula_bound :
  (((40415455378951173001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 16 47) ∧
  (vasyuninBEntryFormula 16 47 ≤ ((20208853589383624437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 16 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log16 := prim_log_16_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_16_47_bounds
  have b_Vkh := cotangentSumVFormula_47_16_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_16_47_lower, cotangentSumVFormula_16_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_16_lower, cotangentSumVFormula_47_16_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_47_unfold :
    cotangentSumVFormula 17 47 =
      ((17/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 17 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_17_47_lower : ℚ := -1518358529182163307979 / 439804651110400000000
def cotangentSumVFormula_17_47_upper : ℚ := -1518358520385683567021 / 439804651110400000000
theorem cotangentSumVFormula_17_47_bounds :
  ((cotangentSumVFormula_17_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 47 ∧
  cotangentSumVFormula 17 47 ≤ ((cotangentSumVFormula_17_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_47_unfold]
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
  rw [cotangentSumVFormula_17_47_lower, cotangentSumVFormula_17_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_17_unfold :
    cotangentSumVFormula 47 17 =
      ((13/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_47_17_lower : ℚ := 1559538363838561274667 / 879609302220800000000
def cotangentSumVFormula_47_17_upper : ℚ := 1559538381430812162833 / 879609302220800000000
theorem cotangentSumVFormula_47_17_bounds :
  ((cotangentSumVFormula_47_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 17 ∧
  cotangentSumVFormula 47 17 ≤ ((cotangentSumVFormula_47_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_17_unfold]
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
  rw [cotangentSumVFormula_47_17_lower, cotangentSumVFormula_47_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1747_formula_bound :
  (((78134581517029892877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 47) ∧
  (vasyuninBEntryFormula 17 47 ≤ ((78139085116661794623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_17_47_bounds
  have b_Vkh := cotangentSumVFormula_47_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_17_47_lower, cotangentSumVFormula_17_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_17_lower, cotangentSumVFormula_47_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_18_47_unfold :
    cotangentSumVFormula 18 47 =
      ((18/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 18 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_18_47_lower : ℚ := -2183110491027505966291 / 1759218604441600000000
def cotangentSumVFormula_18_47_upper : ℚ := -2183110455841612783709 / 1759218604441600000000
theorem cotangentSumVFormula_18_47_bounds :
  ((cotangentSumVFormula_18_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 47 ∧
  cotangentSumVFormula 18 47 ≤ ((cotangentSumVFormula_18_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_47_unfold]
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
  rw [cotangentSumVFormula_18_47_lower, cotangentSumVFormula_18_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_18_unfold :
    cotangentSumVFormula 47 18 =
      ((11/18 : ℚ) : ℝ) * cotangentTermV 1 18    + 
      ((4/18 : ℚ) : ℝ) * cotangentTermV 2 18    + 
      ((15/18 : ℚ) : ℝ) * cotangentTermV 3 18    + 
      ((8/18 : ℚ) : ℝ) * cotangentTermV 4 18    + 
      ((1/18 : ℚ) : ℝ) * cotangentTermV 5 18    + 
      ((12/18 : ℚ) : ℝ) * cotangentTermV 6 18    + 
      ((5/18 : ℚ) : ℝ) * cotangentTermV 7 18    + 
      ((16/18 : ℚ) : ℝ) * cotangentTermV 8 18    + 
      ((9/18 : ℚ) : ℝ) * cotangentTermV 9 18    + 
      ((2/18 : ℚ) : ℝ) * cotangentTermV 10 18    + 
      ((13/18 : ℚ) : ℝ) * cotangentTermV 11 18    + 
      ((6/18 : ℚ) : ℝ) * cotangentTermV 12 18    + 
      ((17/18 : ℚ) : ℝ) * cotangentTermV 13 18    + 
      ((10/18 : ℚ) : ℝ) * cotangentTermV 14 18    + 
      ((3/18 : ℚ) : ℝ) * cotangentTermV 15 18    + 
      ((14/18 : ℚ) : ℝ) * cotangentTermV 16 18    + 
      ((7/18 : ℚ) : ℝ) * cotangentTermV 17 18 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_18]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_47_18_lower : ℚ := 2507299952449330004047 / 14073748835532800000000
def cotangentSumVFormula_47_18_upper : ℚ := 2507300233925582495953 / 14073748835532800000000
theorem cotangentSumVFormula_47_18_bounds :
  ((cotangentSumVFormula_47_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 18 ∧
  cotangentSumVFormula 47 18 ≤ ((cotangentSumVFormula_47_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_18_unfold]
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
  rw [cotangentSumVFormula_47_18_lower, cotangentSumVFormula_47_18_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1847_formula_bound :
  (((76452975607455424127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 18 47) ∧
  (vasyuninBEntryFormula 18 47 ≤ ((76457479207087107123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 18 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log18 := prim_log_18_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_18_47_bounds
  have b_Vkh := cotangentSumVFormula_47_18_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_18_47_lower, cotangentSumVFormula_18_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_18_lower, cotangentSumVFormula_47_18_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_47_unfold :
    cotangentSumVFormula 19 47 =
      ((19/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 19 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_19_47_lower : ℚ := -206730443034956985763 / 54975581388800000000
def cotangentSumVFormula_19_47_upper : ℚ := -826921767741594322573 / 219902325555200000000
theorem cotangentSumVFormula_19_47_bounds :
  ((cotangentSumVFormula_19_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 47 ∧
  cotangentSumVFormula 19 47 ≤ ((cotangentSumVFormula_19_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_47_unfold]
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
  rw [cotangentSumVFormula_19_47_lower, cotangentSumVFormula_19_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_19_unfold :
    cotangentSumVFormula 47 19 =
      ((9/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_47_19_lower : ℚ := 2783035433767551899667 / 879609302220800000000
def cotangentSumVFormula_47_19_upper : ℚ := 2783035451359827787833 / 879609302220800000000
theorem cotangentSumVFormula_47_19_bounds :
  ((cotangentSumVFormula_47_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 19 ∧
  cotangentSumVFormula 47 19 ≤ ((cotangentSumVFormula_47_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_19_unfold]
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
  rw [cotangentSumVFormula_47_19_lower, cotangentSumVFormula_47_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1947_formula_bound :
  (((75290123235443924127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 47) ∧
  (vasyuninBEntryFormula 19 47 ≤ ((75294626835075325873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_19_47_bounds
  have b_Vkh := cotangentSumVFormula_47_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_19_47_lower, cotangentSumVFormula_19_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_19_lower, cotangentSumVFormula_47_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_20_47_unfold :
    cotangentSumVFormula 20 47 =
      ((20/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 20 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_20_47_lower : ℚ := 1147884273301092160771 / 439804651110400000000
def cotangentSumVFormula_20_47_upper : ℚ := 1147884282097554714229 / 439804651110400000000
theorem cotangentSumVFormula_20_47_bounds :
  ((cotangentSumVFormula_20_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 47 ∧
  cotangentSumVFormula 20 47 ≤ ((cotangentSumVFormula_20_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_47_unfold]
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
  rw [cotangentSumVFormula_20_47_lower, cotangentSumVFormula_20_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_20_unfold :
    cotangentSumVFormula 47 20 =
      ((7/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((9/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_47_20_lower : ℚ := -2421372431136839506583 / 879609302220800000000
def cotangentSumVFormula_47_20_upper : ℚ := -2421372413544551118417 / 879609302220800000000
theorem cotangentSumVFormula_47_20_bounds :
  ((cotangentSumVFormula_47_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 20 ∧
  cotangentSumVFormula 47 20 ≤ ((cotangentSumVFormula_47_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_20_unfold]
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
  rw [cotangentSumVFormula_47_20_lower, cotangentSumVFormula_47_20_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2047_formula_bound :
  (((74072025364195017877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 20 47) ∧
  (vasyuninBEntryFormula 20 47 ≤ ((74076528963826263373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 20 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log20 := prim_log_20_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_20_47_bounds
  have b_Vkh := cotangentSumVFormula_47_20_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_20_47_lower, cotangentSumVFormula_20_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_20_lower, cotangentSumVFormula_47_20_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_21_47_unfold :
    cotangentSumVFormula 21 47 =
      ((21/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 21 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_21_47_lower : ℚ := 112635269605639107987 / 54975581388800000000
def cotangentSumVFormula_21_47_upper : ℚ := 225270541410390924651 / 109951162777600000000
theorem cotangentSumVFormula_21_47_bounds :
  ((cotangentSumVFormula_21_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 21 47 ∧
  cotangentSumVFormula 21 47 ≤ ((cotangentSumVFormula_21_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_21_47_unfold]
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
  rw [cotangentSumVFormula_21_47_lower, cotangentSumVFormula_21_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_21_unfold :
    cotangentSumVFormula 47 21 =
      ((5/21 : ℚ) : ℝ) * cotangentTermV 1 21    + 
      ((10/21 : ℚ) : ℝ) * cotangentTermV 2 21    + 
      ((15/21 : ℚ) : ℝ) * cotangentTermV 3 21    + 
      ((20/21 : ℚ) : ℝ) * cotangentTermV 4 21    + 
      ((4/21 : ℚ) : ℝ) * cotangentTermV 5 21    + 
      ((9/21 : ℚ) : ℝ) * cotangentTermV 6 21    + 
      ((14/21 : ℚ) : ℝ) * cotangentTermV 7 21    + 
      ((19/21 : ℚ) : ℝ) * cotangentTermV 8 21    + 
      ((3/21 : ℚ) : ℝ) * cotangentTermV 9 21    + 
      ((8/21 : ℚ) : ℝ) * cotangentTermV 10 21    + 
      ((13/21 : ℚ) : ℝ) * cotangentTermV 11 21    + 
      ((18/21 : ℚ) : ℝ) * cotangentTermV 12 21    + 
      ((2/21 : ℚ) : ℝ) * cotangentTermV 13 21    + 
      ((7/21 : ℚ) : ℝ) * cotangentTermV 14 21    + 
      ((12/21 : ℚ) : ℝ) * cotangentTermV 15 21    + 
      ((17/21 : ℚ) : ℝ) * cotangentTermV 16 21    + 
      ((1/21 : ℚ) : ℝ) * cotangentTermV 17 21    + 
      ((6/21 : ℚ) : ℝ) * cotangentTermV 18 21    + 
      ((11/21 : ℚ) : ℝ) * cotangentTermV 19 21    + 
      ((16/21 : ℚ) : ℝ) * cotangentTermV 20 21 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_21]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((5/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((10/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((15/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((20/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((4/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((9/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((14/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((19/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((3/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((8/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((13/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((18/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((2/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((7/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((12/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((17/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((1/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((6/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((11/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((16/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20]
  try ring

def cotangentSumVFormula_47_21_lower : ℚ := -3279984007206159091291 / 1759218604441600000000
def cotangentSumVFormula_47_21_upper : ℚ := -3279983972021578408709 / 1759218604441600000000
theorem cotangentSumVFormula_47_21_bounds :
  ((cotangentSumVFormula_47_21_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 21 ∧
  cotangentSumVFormula 47 21 ≤ ((cotangentSumVFormula_47_21_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_21_unfold]
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
  rw [cotangentSumVFormula_47_21_lower, cotangentSumVFormula_47_21_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2147_formula_bound :
  (((73232016041818142877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 21 47) ∧
  (vasyuninBEntryFormula 21 47 ≤ ((73236519641449138373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 21 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log21 := prim_log_21_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_21_47_bounds
  have b_Vkh := cotangentSumVFormula_47_21_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_21_lower, prim_log_21_upper] at b_log21
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_21_47_lower, cotangentSumVFormula_21_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_21_lower, cotangentSumVFormula_47_21_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_22_47_unfold :
    cotangentSumVFormula 22 47 =
      ((22/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 22 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_22_47_lower : ℚ := 2747196191575040598271 / 439804651110400000000
def cotangentSumVFormula_22_47_upper : ℚ := 2747196200371478151729 / 439804651110400000000
theorem cotangentSumVFormula_22_47_bounds :
  ((cotangentSumVFormula_22_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 22 47 ∧
  cotangentSumVFormula 22 47 ≤ ((cotangentSumVFormula_22_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_22_47_unfold]
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
  rw [cotangentSumVFormula_22_47_lower, cotangentSumVFormula_22_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_22_unfold :
    cotangentSumVFormula 47 22 =
      ((3/22 : ℚ) : ℝ) * cotangentTermV 1 22    + 
      ((6/22 : ℚ) : ℝ) * cotangentTermV 2 22    + 
      ((9/22 : ℚ) : ℝ) * cotangentTermV 3 22    + 
      ((12/22 : ℚ) : ℝ) * cotangentTermV 4 22    + 
      ((15/22 : ℚ) : ℝ) * cotangentTermV 5 22    + 
      ((18/22 : ℚ) : ℝ) * cotangentTermV 6 22    + 
      ((21/22 : ℚ) : ℝ) * cotangentTermV 7 22    + 
      ((2/22 : ℚ) : ℝ) * cotangentTermV 8 22    + 
      ((5/22 : ℚ) : ℝ) * cotangentTermV 9 22    + 
      ((8/22 : ℚ) : ℝ) * cotangentTermV 10 22    + 
      ((11/22 : ℚ) : ℝ) * cotangentTermV 11 22    + 
      ((14/22 : ℚ) : ℝ) * cotangentTermV 12 22    + 
      ((17/22 : ℚ) : ℝ) * cotangentTermV 13 22    + 
      ((20/22 : ℚ) : ℝ) * cotangentTermV 14 22    + 
      ((1/22 : ℚ) : ℝ) * cotangentTermV 15 22    + 
      ((4/22 : ℚ) : ℝ) * cotangentTermV 16 22    + 
      ((7/22 : ℚ) : ℝ) * cotangentTermV 17 22    + 
      ((10/22 : ℚ) : ℝ) * cotangentTermV 18 22    + 
      ((13/22 : ℚ) : ℝ) * cotangentTermV 19 22    + 
      ((16/22 : ℚ) : ℝ) * cotangentTermV 20 22    + 
      ((19/22 : ℚ) : ℝ) * cotangentTermV 21 22 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_22]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((3/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((6/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((9/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((12/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((15/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((18/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((21/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((2/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((5/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((8/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((11/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((14/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((17/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((20/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((1/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((4/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((7/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((10/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((13/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((16/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((19/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21]
  try ring

def cotangentSumVFormula_47_22_lower : ℚ := -80823953980197156597 / 13743895347200000000
def cotangentSumVFormula_47_22_upper : ℚ := -1293183259285065416323 / 219902325555200000000
theorem cotangentSumVFormula_47_22_bounds :
  ((cotangentSumVFormula_47_22_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 22 ∧
  cotangentSumVFormula 47 22 ≤ ((cotangentSumVFormula_47_22_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_22_unfold]
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
  rw [cotangentSumVFormula_47_22_lower, cotangentSumVFormula_47_22_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2247_formula_bound :
  (((72799238421913799127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 22 47) ∧
  (vasyuninBEntryFormula 22 47 ≤ ((72803742021544763373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 22 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log22 := prim_log_22_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_22_47_bounds
  have b_Vkh := cotangentSumVFormula_47_22_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_22_lower, prim_log_22_upper] at b_log22
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_22_47_lower, cotangentSumVFormula_22_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_22_lower, cotangentSumVFormula_47_22_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_47_unfold :
    cotangentSumVFormula 23 47 =
      ((23/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 23 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_23_47_lower : ℚ := 788790697789609420487 / 54975581388800000000
def cotangentSumVFormula_23_47_upper : ℚ := 1577581397778326862151 / 109951162777600000000
theorem cotangentSumVFormula_23_47_bounds :
  ((cotangentSumVFormula_23_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 47 ∧
  cotangentSumVFormula 23 47 ≤ ((cotangentSumVFormula_23_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_47_unfold]
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
  rw [cotangentSumVFormula_23_47_lower, cotangentSumVFormula_23_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_23_unfold :
    cotangentSumVFormula 47 23 =
      ((1/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_47_23_lower : ℚ := -1544593217097112799651 / 109951162777600000000
def cotangentSumVFormula_47_23_upper : ℚ := -772296607449032076737 / 54975581388800000000
theorem cotangentSumVFormula_47_23_bounds :
  ((cotangentSumVFormula_47_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 23 ∧
  cotangentSumVFormula 47 23 ≤ ((cotangentSumVFormula_47_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_23_unfold]
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
  rw [cotangentSumVFormula_47_23_lower, cotangentSumVFormula_47_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2347_formula_bound :
  (((73063609182364736627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 47) ∧
  (vasyuninBEntryFormula 23 47 ≤ ((73068112781995669623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_23_47_bounds
  have b_Vkh := cotangentSumVFormula_47_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_23_47_lower, cotangentSumVFormula_23_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_23_lower, cotangentSumVFormula_47_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_24_47_unfold :
    cotangentSumVFormula 24 47 =
      ((24/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 24 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_24_47_lower : ℚ := -3155162795556636146177 / 219902325555200000000
def cotangentSumVFormula_24_47_upper : ℚ := -3155162791158406822573 / 219902325555200000000
theorem cotangentSumVFormula_24_47_bounds :
  ((cotangentSumVFormula_24_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 24 47 ∧
  cotangentSumVFormula 24 47 ≤ ((cotangentSumVFormula_24_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_24_47_unfold]
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
  rw [cotangentSumVFormula_24_47_lower, cotangentSumVFormula_24_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_24_unfold :
    cotangentSumVFormula 47 24 =
      ((23/24 : ℚ) : ℝ) * cotangentTermV 1 24    + 
      ((22/24 : ℚ) : ℝ) * cotangentTermV 2 24    + 
      ((21/24 : ℚ) : ℝ) * cotangentTermV 3 24    + 
      ((20/24 : ℚ) : ℝ) * cotangentTermV 4 24    + 
      ((19/24 : ℚ) : ℝ) * cotangentTermV 5 24    + 
      ((18/24 : ℚ) : ℝ) * cotangentTermV 6 24    + 
      ((17/24 : ℚ) : ℝ) * cotangentTermV 7 24    + 
      ((16/24 : ℚ) : ℝ) * cotangentTermV 8 24    + 
      ((15/24 : ℚ) : ℝ) * cotangentTermV 9 24    + 
      ((14/24 : ℚ) : ℝ) * cotangentTermV 10 24    + 
      ((13/24 : ℚ) : ℝ) * cotangentTermV 11 24    + 
      ((12/24 : ℚ) : ℝ) * cotangentTermV 12 24    + 
      ((11/24 : ℚ) : ℝ) * cotangentTermV 13 24    + 
      ((10/24 : ℚ) : ℝ) * cotangentTermV 14 24    + 
      ((9/24 : ℚ) : ℝ) * cotangentTermV 15 24    + 
      ((8/24 : ℚ) : ℝ) * cotangentTermV 16 24    + 
      ((7/24 : ℚ) : ℝ) * cotangentTermV 17 24    + 
      ((6/24 : ℚ) : ℝ) * cotangentTermV 18 24    + 
      ((5/24 : ℚ) : ℝ) * cotangentTermV 19 24    + 
      ((4/24 : ℚ) : ℝ) * cotangentTermV 20 24    + 
      ((3/24 : ℚ) : ℝ) * cotangentTermV 21 24    + 
      ((2/24 : ℚ) : ℝ) * cotangentTermV 22 24    + 
      ((1/24 : ℚ) : ℝ) * cotangentTermV 23 24 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_24]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((23/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((22/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((21/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((20/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((19/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((18/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((17/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((16/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((15/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((14/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((13/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((12/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((11/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((10/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((9/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((8/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((7/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((6/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((5/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((4/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((3/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((2/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((1/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23]
  try ring

def cotangentSumVFormula_47_24_lower : ℚ := 822970420477745357987 / 54975581388800000000
def cotangentSumVFormula_47_24_upper : ℚ := 205742605394316687847 / 13743895347200000000
theorem cotangentSumVFormula_47_24_bounds :
  ((cotangentSumVFormula_47_24_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 24 ∧
  cotangentSumVFormula 47 24 ≤ ((cotangentSumVFormula_47_24_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_24_unfold]
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
  rw [cotangentSumVFormula_47_24_lower, cotangentSumVFormula_47_24_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2447_formula_bound :
  (((71959116120599799127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 24 47) ∧
  (vasyuninBEntryFormula 24 47 ≤ ((71963619720230607123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 24 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log24 := prim_log_24_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_24_47_bounds
  have b_Vkh := cotangentSumVFormula_47_24_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_24_lower, prim_log_24_upper] at b_log24
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_24_47_lower, cotangentSumVFormula_24_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_24_lower, cotangentSumVFormula_47_24_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_25_47_unfold :
    cotangentSumVFormula 25 47 =
      ((25/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 25 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_25_47_lower : ℚ := -1373598100185720521177 / 219902325555200000000
def cotangentSumVFormula_25_47_upper : ℚ := -42924940493359038889 / 6871947673600000000
theorem cotangentSumVFormula_25_47_bounds :
  ((cotangentSumVFormula_25_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 47 ∧
  cotangentSumVFormula 25 47 ≤ ((cotangentSumVFormula_25_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_47_unfold]
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
  rw [cotangentSumVFormula_25_47_lower, cotangentSumVFormula_25_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_25_unfold :
    cotangentSumVFormula 47 25 =
      ((22/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((19/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((17/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((14/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((11/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((24/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((21/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((12/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_47_25_lower : ℚ := 1670701435817119322573 / 219902325555200000000
def cotangentSumVFormula_47_25_upper : ℚ := 1670701440215200989927 / 219902325555200000000
theorem cotangentSumVFormula_47_25_bounds :
  ((cotangentSumVFormula_47_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 25 ∧
  cotangentSumVFormula 47 25 ≤ ((cotangentSumVFormula_47_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_25_unfold]
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
  rw [cotangentSumVFormula_47_25_lower, cotangentSumVFormula_47_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2547_formula_bound :
  (((139195305572472957629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 47) ∧
  (vasyuninBEntryFormula 25 47 ≤ ((139204312771734198621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_25_47_bounds
  have b_Vkh := cotangentSumVFormula_47_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_25_47_lower, cotangentSumVFormula_25_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_25_lower, cotangentSumVFormula_47_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_26_47_unfold :
    cotangentSumVFormula 26 47 =
      ((26/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 26 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_26_47_lower : ℚ := -901082165641525807979 / 439804651110400000000
def cotangentSumVFormula_26_47_upper : ℚ := -901082156845067160771 / 439804651110400000000
theorem cotangentSumVFormula_26_47_bounds :
  ((cotangentSumVFormula_26_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 26 47 ∧
  cotangentSumVFormula 26 47 ≤ ((cotangentSumVFormula_26_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_26_47_unfold]
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
  rw [cotangentSumVFormula_26_47_lower, cotangentSumVFormula_26_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_26_unfold :
    cotangentSumVFormula 47 26 =
      ((21/26 : ℚ) : ℝ) * cotangentTermV 1 26    + 
      ((16/26 : ℚ) : ℝ) * cotangentTermV 2 26    + 
      ((11/26 : ℚ) : ℝ) * cotangentTermV 3 26    + 
      ((6/26 : ℚ) : ℝ) * cotangentTermV 4 26    + 
      ((1/26 : ℚ) : ℝ) * cotangentTermV 5 26    + 
      ((22/26 : ℚ) : ℝ) * cotangentTermV 6 26    + 
      ((17/26 : ℚ) : ℝ) * cotangentTermV 7 26    + 
      ((12/26 : ℚ) : ℝ) * cotangentTermV 8 26    + 
      ((7/26 : ℚ) : ℝ) * cotangentTermV 9 26    + 
      ((2/26 : ℚ) : ℝ) * cotangentTermV 10 26    + 
      ((23/26 : ℚ) : ℝ) * cotangentTermV 11 26    + 
      ((18/26 : ℚ) : ℝ) * cotangentTermV 12 26    + 
      ((13/26 : ℚ) : ℝ) * cotangentTermV 13 26    + 
      ((8/26 : ℚ) : ℝ) * cotangentTermV 14 26    + 
      ((3/26 : ℚ) : ℝ) * cotangentTermV 15 26    + 
      ((24/26 : ℚ) : ℝ) * cotangentTermV 16 26    + 
      ((19/26 : ℚ) : ℝ) * cotangentTermV 17 26    + 
      ((14/26 : ℚ) : ℝ) * cotangentTermV 18 26    + 
      ((9/26 : ℚ) : ℝ) * cotangentTermV 19 26    + 
      ((4/26 : ℚ) : ℝ) * cotangentTermV 20 26    + 
      ((25/26 : ℚ) : ℝ) * cotangentTermV 21 26    + 
      ((20/26 : ℚ) : ℝ) * cotangentTermV 22 26    + 
      ((15/26 : ℚ) : ℝ) * cotangentTermV 23 26    + 
      ((10/26 : ℚ) : ℝ) * cotangentTermV 24 26    + 
      ((5/26 : ℚ) : ℝ) * cotangentTermV 25 26 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_26]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((21/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((16/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((11/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((6/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((1/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((22/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((17/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((12/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((7/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((2/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((23/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((18/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((13/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((8/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((3/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((24/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((19/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((14/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((9/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((4/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((25/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((20/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((15/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((10/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((5/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25]
  try ring

def cotangentSumVFormula_47_26_lower : ℚ := 1719463267692014817021 / 439804651110400000000
def cotangentSumVFormula_47_26_upper : ℚ := 214932909561023392013 / 54975581388800000000
theorem cotangentSumVFormula_47_26_bounds :
  ((cotangentSumVFormula_47_26_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 26 ∧
  cotangentSumVFormula 47 26 ≤ ((cotangentSumVFormula_47_26_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_26_unfold]
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
  rw [cotangentSumVFormula_47_26_lower, cotangentSumVFormula_47_26_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2647_formula_bound :
  (((135894724017322113879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 26 47) ∧
  (vasyuninBEntryFormula 26 47 ≤ ((135903731216583167371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 26 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log26 := prim_log_26_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_26_47_bounds
  have b_Vkh := cotangentSumVFormula_47_26_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_26_lower, prim_log_26_upper] at b_log26
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_26_47_lower, cotangentSumVFormula_26_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_26_lower, cotangentSumVFormula_47_26_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_27_47_unfold :
    cotangentSumVFormula 27 47 =
      ((27/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 27 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_27_47_lower : ℚ := -1147884282097496901729 / 439804651110400000000
def cotangentSumVFormula_27_47_upper : ℚ := -1147884273301053879521 / 439804651110400000000
theorem cotangentSumVFormula_27_47_bounds :
  ((cotangentSumVFormula_27_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 27 47 ∧
  cotangentSumVFormula 27 47 ≤ ((cotangentSumVFormula_27_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_27_47_unfold]
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
  rw [cotangentSumVFormula_27_47_lower, cotangentSumVFormula_27_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_27_unfold :
    cotangentSumVFormula 47 27 =
      ((20/27 : ℚ) : ℝ) * cotangentTermV 1 27    + 
      ((13/27 : ℚ) : ℝ) * cotangentTermV 2 27    + 
      ((6/27 : ℚ) : ℝ) * cotangentTermV 3 27    + 
      ((26/27 : ℚ) : ℝ) * cotangentTermV 4 27    + 
      ((19/27 : ℚ) : ℝ) * cotangentTermV 5 27    + 
      ((12/27 : ℚ) : ℝ) * cotangentTermV 6 27    + 
      ((5/27 : ℚ) : ℝ) * cotangentTermV 7 27    + 
      ((25/27 : ℚ) : ℝ) * cotangentTermV 8 27    + 
      ((18/27 : ℚ) : ℝ) * cotangentTermV 9 27    + 
      ((11/27 : ℚ) : ℝ) * cotangentTermV 10 27    + 
      ((4/27 : ℚ) : ℝ) * cotangentTermV 11 27    + 
      ((24/27 : ℚ) : ℝ) * cotangentTermV 12 27    + 
      ((17/27 : ℚ) : ℝ) * cotangentTermV 13 27    + 
      ((10/27 : ℚ) : ℝ) * cotangentTermV 14 27    + 
      ((3/27 : ℚ) : ℝ) * cotangentTermV 15 27    + 
      ((23/27 : ℚ) : ℝ) * cotangentTermV 16 27    + 
      ((16/27 : ℚ) : ℝ) * cotangentTermV 17 27    + 
      ((9/27 : ℚ) : ℝ) * cotangentTermV 18 27    + 
      ((2/27 : ℚ) : ℝ) * cotangentTermV 19 27    + 
      ((22/27 : ℚ) : ℝ) * cotangentTermV 20 27    + 
      ((15/27 : ℚ) : ℝ) * cotangentTermV 21 27    + 
      ((8/27 : ℚ) : ℝ) * cotangentTermV 22 27    + 
      ((1/27 : ℚ) : ℝ) * cotangentTermV 23 27    + 
      ((21/27 : ℚ) : ℝ) * cotangentTermV 24 27    + 
      ((14/27 : ℚ) : ℝ) * cotangentTermV 25 27    + 
      ((7/27 : ℚ) : ℝ) * cotangentTermV 26 27 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_27]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((20/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((13/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((6/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((26/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((19/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((12/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((5/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((25/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((18/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((11/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((4/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((24/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((17/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((10/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((3/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((23/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((16/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((9/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((2/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((22/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((15/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((8/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((1/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((21/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((14/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((7/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26]
  try ring

def cotangentSumVFormula_47_27_lower : ℚ := 2138184158691028098271 / 439804651110400000000
def cotangentSumVFormula_47_27_upper : ℚ := 2138184167487213307979 / 439804651110400000000
theorem cotangentSumVFormula_47_27_bounds :
  ((cotangentSumVFormula_47_27_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 27 ∧
  cotangentSumVFormula 47 27 ≤ ((cotangentSumVFormula_47_27_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_27_unfold]
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
  rw [cotangentSumVFormula_47_27_lower, cotangentSumVFormula_47_27_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2747_formula_bound :
  (((133309256333840457629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 27 47) ∧
  (vasyuninBEntryFormula 27 47 ≤ ((133318263533101229871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 27 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log27 := prim_log_27_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_27_47_bounds
  have b_Vkh := cotangentSumVFormula_47_27_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_27_lower, prim_log_27_upper] at b_log27
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_27_47_lower, cotangentSumVFormula_27_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_27_lower, cotangentSumVFormula_47_27_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_28_47_unfold :
    cotangentSumVFormula 28 47 =
      ((28/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 28 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_28_47_lower : ℚ := 3307687070966483930917 / 879609302220800000000
def cotangentSumVFormula_28_47_upper : ℚ := 3307687088559372319083 / 879609302220800000000
theorem cotangentSumVFormula_28_47_bounds :
  ((cotangentSumVFormula_28_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 28 47 ∧
  cotangentSumVFormula 28 47 ≤ ((cotangentSumVFormula_28_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_28_47_unfold]
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
  rw [cotangentSumVFormula_28_47_lower, cotangentSumVFormula_28_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_28_unfold :
    cotangentSumVFormula 47 28 =
      ((19/28 : ℚ) : ℝ) * cotangentTermV 1 28    + 
      ((10/28 : ℚ) : ℝ) * cotangentTermV 2 28    + 
      ((1/28 : ℚ) : ℝ) * cotangentTermV 3 28    + 
      ((20/28 : ℚ) : ℝ) * cotangentTermV 4 28    + 
      ((11/28 : ℚ) : ℝ) * cotangentTermV 5 28    + 
      ((2/28 : ℚ) : ℝ) * cotangentTermV 6 28    + 
      ((21/28 : ℚ) : ℝ) * cotangentTermV 7 28    + 
      ((12/28 : ℚ) : ℝ) * cotangentTermV 8 28    + 
      ((3/28 : ℚ) : ℝ) * cotangentTermV 9 28    + 
      ((22/28 : ℚ) : ℝ) * cotangentTermV 10 28    + 
      ((13/28 : ℚ) : ℝ) * cotangentTermV 11 28    + 
      ((4/28 : ℚ) : ℝ) * cotangentTermV 12 28    + 
      ((23/28 : ℚ) : ℝ) * cotangentTermV 13 28    + 
      ((14/28 : ℚ) : ℝ) * cotangentTermV 14 28    + 
      ((5/28 : ℚ) : ℝ) * cotangentTermV 15 28    + 
      ((24/28 : ℚ) : ℝ) * cotangentTermV 16 28    + 
      ((15/28 : ℚ) : ℝ) * cotangentTermV 17 28    + 
      ((6/28 : ℚ) : ℝ) * cotangentTermV 18 28    + 
      ((25/28 : ℚ) : ℝ) * cotangentTermV 19 28    + 
      ((16/28 : ℚ) : ℝ) * cotangentTermV 20 28    + 
      ((7/28 : ℚ) : ℝ) * cotangentTermV 21 28    + 
      ((26/28 : ℚ) : ℝ) * cotangentTermV 22 28    + 
      ((17/28 : ℚ) : ℝ) * cotangentTermV 23 28    + 
      ((8/28 : ℚ) : ℝ) * cotangentTermV 24 28    + 
      ((27/28 : ℚ) : ℝ) * cotangentTermV 25 28    + 
      ((18/28 : ℚ) : ℝ) * cotangentTermV 26 28    + 
      ((9/28 : ℚ) : ℝ) * cotangentTermV 27 28 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_28]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((19/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((10/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((1/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((20/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((11/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((2/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((21/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((12/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((3/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((22/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((13/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((4/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((23/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((14/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((5/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((24/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((15/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((6/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((25/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((16/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((7/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((26/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((17/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((8/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((27/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((18/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((28 : ℕ) : ℝ)) = ((9/28 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27]
  try ring

def cotangentSumVFormula_47_28_lower : ℚ := -2128158540199787216291 / 1759218604441600000000
def cotangentSumVFormula_47_28_upper : ℚ := -2128158505014997158709 / 1759218604441600000000
theorem cotangentSumVFormula_47_28_bounds :
  ((cotangentSumVFormula_47_28_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 28 ∧
  cotangentSumVFormula 47 28 ≤ ((cotangentSumVFormula_47_28_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_28_unfold]
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
  rw [cotangentSumVFormula_47_28_lower, cotangentSumVFormula_47_28_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2847_formula_bound :
  (((131228657102423238879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 28 47) ∧
  (vasyuninBEntryFormula 28 47 ≤ ((131237664301683979871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 28 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log28 := prim_log_28_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_28_47_bounds
  have b_Vkh := cotangentSumVFormula_47_28_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_28_lower, prim_log_28_upper] at b_log28
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_28_47_lower, cotangentSumVFormula_28_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_28_lower, cotangentSumVFormula_47_28_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_47_unfold :
    cotangentSumVFormula 29 47 =
      ((29/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 29 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_29_47_lower : ℚ := 272888806980235728823 / 219902325555200000000
def cotangentSumVFormula_29_47_upper : ℚ := 272888811378454114927 / 219902325555200000000
theorem cotangentSumVFormula_29_47_bounds :
  ((cotangentSumVFormula_29_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 47 ∧
  cotangentSumVFormula 29 47 ≤ ((cotangentSumVFormula_29_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_47_unfold]
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
  rw [cotangentSumVFormula_29_47_lower, cotangentSumVFormula_29_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_29_unfold :
    cotangentSumVFormula 47 29 =
      ((18/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_47_29_lower : ℚ := 2808850794911519814959 / 1759218604441600000000
def cotangentSumVFormula_47_29_upper : ℚ := 2808850830096306747541 / 1759218604441600000000
theorem cotangentSumVFormula_47_29_bounds :
  ((cotangentSumVFormula_47_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 29 ∧
  cotangentSumVFormula 47 29 ≤ ((cotangentSumVFormula_47_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_29_unfold]
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
  rw [cotangentSumVFormula_47_29_lower, cotangentSumVFormula_47_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2947_formula_bound :
  (((129196181182531270129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 47) ∧
  (vasyuninBEntryFormula 29 47 ≤ ((129205188381791729871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_29_47_bounds
  have b_Vkh := cotangentSumVFormula_47_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_29_47_lower, cotangentSumVFormula_29_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_29_lower, cotangentSumVFormula_47_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
