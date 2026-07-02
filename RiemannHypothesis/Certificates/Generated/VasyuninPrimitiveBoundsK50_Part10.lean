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

theorem cotangentSumVFormula_30_47_unfold :
    cotangentSumVFormula 30 47 =
      ((30/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 30 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_30_47_lower : ℚ := 2965543985128424783 / 858993459200000000
def cotangentSumVFormula_30_47_upper : ℚ := 759179264591093177427 / 219902325555200000000
theorem cotangentSumVFormula_30_47_bounds :
  ((cotangentSumVFormula_30_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 30 47 ∧
  cotangentSumVFormula 30 47 ≤ ((cotangentSumVFormula_30_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_30_47_unfold]
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
  rw [cotangentSumVFormula_30_47_lower, cotangentSumVFormula_30_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_30_unfold :
    cotangentSumVFormula 47 30 =
      ((17/30 : ℚ) : ℝ) * cotangentTermV 1 30    + 
      ((4/30 : ℚ) : ℝ) * cotangentTermV 2 30    + 
      ((21/30 : ℚ) : ℝ) * cotangentTermV 3 30    + 
      ((8/30 : ℚ) : ℝ) * cotangentTermV 4 30    + 
      ((25/30 : ℚ) : ℝ) * cotangentTermV 5 30    + 
      ((12/30 : ℚ) : ℝ) * cotangentTermV 6 30    + 
      ((29/30 : ℚ) : ℝ) * cotangentTermV 7 30    + 
      ((16/30 : ℚ) : ℝ) * cotangentTermV 8 30    + 
      ((3/30 : ℚ) : ℝ) * cotangentTermV 9 30    + 
      ((20/30 : ℚ) : ℝ) * cotangentTermV 10 30    + 
      ((7/30 : ℚ) : ℝ) * cotangentTermV 11 30    + 
      ((24/30 : ℚ) : ℝ) * cotangentTermV 12 30    + 
      ((11/30 : ℚ) : ℝ) * cotangentTermV 13 30    + 
      ((28/30 : ℚ) : ℝ) * cotangentTermV 14 30    + 
      ((15/30 : ℚ) : ℝ) * cotangentTermV 15 30    + 
      ((2/30 : ℚ) : ℝ) * cotangentTermV 16 30    + 
      ((19/30 : ℚ) : ℝ) * cotangentTermV 17 30    + 
      ((6/30 : ℚ) : ℝ) * cotangentTermV 18 30    + 
      ((23/30 : ℚ) : ℝ) * cotangentTermV 19 30    + 
      ((10/30 : ℚ) : ℝ) * cotangentTermV 20 30    + 
      ((27/30 : ℚ) : ℝ) * cotangentTermV 21 30    + 
      ((14/30 : ℚ) : ℝ) * cotangentTermV 22 30    + 
      ((1/30 : ℚ) : ℝ) * cotangentTermV 23 30    + 
      ((18/30 : ℚ) : ℝ) * cotangentTermV 24 30    + 
      ((5/30 : ℚ) : ℝ) * cotangentTermV 25 30    + 
      ((22/30 : ℚ) : ℝ) * cotangentTermV 26 30    + 
      ((9/30 : ℚ) : ℝ) * cotangentTermV 27 30    + 
      ((26/30 : ℚ) : ℝ) * cotangentTermV 28 30    + 
      ((13/30 : ℚ) : ℝ) * cotangentTermV 29 30 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_30]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((17/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((4/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((21/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((8/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((25/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((12/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((29/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((16/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((3/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((20/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((7/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((24/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((11/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((28/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((15/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((2/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((19/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((6/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((23/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((10/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((27/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((14/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((1/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((18/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((5/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((22/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((9/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((26/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((30 : ℕ) : ℝ)) = ((13/30 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29]
  try ring

def cotangentSumVFormula_47_30_lower : ℚ := -2951358706524688318289 / 7036874417766400000000
def cotangentSumVFormula_47_30_upper : ℚ := -2951358565785261681711 / 7036874417766400000000
theorem cotangentSumVFormula_47_30_bounds :
  ((cotangentSumVFormula_47_30_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 30 ∧
  cotangentSumVFormula 47 30 ≤ ((cotangentSumVFormula_47_30_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_30_unfold]
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
  rw [cotangentSumVFormula_47_30_lower, cotangentSumVFormula_47_30_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3047_formula_bound :
  (((63807151294458892877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 30 47) ∧
  (vasyuninBEntryFormula 30 47 ≤ ((63811654894089107123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 30 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log30 := prim_log_30_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_30_47_bounds
  have b_Vkh := cotangentSumVFormula_47_30_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_30_lower, prim_log_30_upper] at b_log30
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_30_47_lower, cotangentSumVFormula_30_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_30_lower, cotangentSumVFormula_47_30_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_47_unfold :
    cotangentSumVFormula 31 47 =
      ((31/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 31 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_31_47_lower : ℚ := 1161248683063680169099 / 109951162777600000000
def cotangentSumVFormula_31_47_upper : ℚ := 290312171315696266319 / 27487790694400000000
theorem cotangentSumVFormula_31_47_bounds :
  ((cotangentSumVFormula_31_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 47 ∧
  cotangentSumVFormula 31 47 ≤ ((cotangentSumVFormula_31_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_47_unfold]
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
  rw [cotangentSumVFormula_31_47_lower, cotangentSumVFormula_31_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_31_unfold :
    cotangentSumVFormula 47 31 =
      ((16/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_47_31_lower : ℚ := -3284326371888650026729 / 439804651110400000000
def cotangentSumVFormula_47_31_upper : ℚ := -3284326363092411692021 / 439804651110400000000
theorem cotangentSumVFormula_47_31_bounds :
  ((cotangentSumVFormula_47_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 31 ∧
  cotangentSumVFormula 47 31 ≤ ((cotangentSumVFormula_47_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_31_unfold]
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
  rw [cotangentSumVFormula_47_31_lower, cotangentSumVFormula_47_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3147_formula_bound :
  (((31663768982187923001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 47) ∧
  (vasyuninBEntryFormula 31 47 ≤ ((63332041564006013373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_31_47_bounds
  have b_Vkh := cotangentSumVFormula_47_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_31_47_lower, cotangentSumVFormula_31_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_31_lower, cotangentSumVFormula_47_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_32_47_unfold :
    cotangentSumVFormula 32 47 =
      ((32/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 32 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_32_47_lower : ℚ := -2062746237776323153791 / 1759218604441600000000
def cotangentSumVFormula_32_47_upper : ℚ := -2062746202590598721209 / 1759218604441600000000
theorem cotangentSumVFormula_32_47_bounds :
  ((cotangentSumVFormula_32_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 32 47 ∧
  cotangentSumVFormula 32 47 ≤ ((cotangentSumVFormula_32_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_32_47_unfold]
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
  rw [cotangentSumVFormula_32_47_lower, cotangentSumVFormula_32_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_32_unfold :
    cotangentSumVFormula 47 32 =
      ((15/32 : ℚ) : ℝ) * cotangentTermV 1 32    + 
      ((30/32 : ℚ) : ℝ) * cotangentTermV 2 32    + 
      ((13/32 : ℚ) : ℝ) * cotangentTermV 3 32    + 
      ((28/32 : ℚ) : ℝ) * cotangentTermV 4 32    + 
      ((11/32 : ℚ) : ℝ) * cotangentTermV 5 32    + 
      ((26/32 : ℚ) : ℝ) * cotangentTermV 6 32    + 
      ((9/32 : ℚ) : ℝ) * cotangentTermV 7 32    + 
      ((24/32 : ℚ) : ℝ) * cotangentTermV 8 32    + 
      ((7/32 : ℚ) : ℝ) * cotangentTermV 9 32    + 
      ((22/32 : ℚ) : ℝ) * cotangentTermV 10 32    + 
      ((5/32 : ℚ) : ℝ) * cotangentTermV 11 32    + 
      ((20/32 : ℚ) : ℝ) * cotangentTermV 12 32    + 
      ((3/32 : ℚ) : ℝ) * cotangentTermV 13 32    + 
      ((18/32 : ℚ) : ℝ) * cotangentTermV 14 32    + 
      ((1/32 : ℚ) : ℝ) * cotangentTermV 15 32    + 
      ((16/32 : ℚ) : ℝ) * cotangentTermV 16 32    + 
      ((31/32 : ℚ) : ℝ) * cotangentTermV 17 32    + 
      ((14/32 : ℚ) : ℝ) * cotangentTermV 18 32    + 
      ((29/32 : ℚ) : ℝ) * cotangentTermV 19 32    + 
      ((12/32 : ℚ) : ℝ) * cotangentTermV 20 32    + 
      ((27/32 : ℚ) : ℝ) * cotangentTermV 21 32    + 
      ((10/32 : ℚ) : ℝ) * cotangentTermV 22 32    + 
      ((25/32 : ℚ) : ℝ) * cotangentTermV 23 32    + 
      ((8/32 : ℚ) : ℝ) * cotangentTermV 24 32    + 
      ((23/32 : ℚ) : ℝ) * cotangentTermV 25 32    + 
      ((6/32 : ℚ) : ℝ) * cotangentTermV 26 32    + 
      ((21/32 : ℚ) : ℝ) * cotangentTermV 27 32    + 
      ((4/32 : ℚ) : ℝ) * cotangentTermV 28 32    + 
      ((19/32 : ℚ) : ℝ) * cotangentTermV 29 32    + 
      ((2/32 : ℚ) : ℝ) * cotangentTermV 30 32    + 
      ((17/32 : ℚ) : ℝ) * cotangentTermV 31 32 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_32]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((15/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((30/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((13/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((28/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((11/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((26/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((9/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((24/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((7/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((22/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((5/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((20/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((3/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((18/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((1/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((16/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((31/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((14/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((29/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((12/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((27/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((10/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((25/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((8/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((23/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((6/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((21/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((4/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((19/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((2/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((17/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31]
  try ring

def cotangentSumVFormula_47_32_lower : ℚ := 1972793312432114817021 / 439804651110400000000
def cotangentSumVFormula_47_32_upper : ℚ := 1972793321228325026729 / 439804651110400000000
theorem cotangentSumVFormula_47_32_bounds :
  ((cotangentSumVFormula_47_32_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 32 ∧
  cotangentSumVFormula 47 32 ≤ ((cotangentSumVFormula_47_32_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_32_unfold]
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
  rw [cotangentSumVFormula_47_32_lower, cotangentSumVFormula_47_32_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3247_formula_bound :
  (((62444570984308986627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 32 47) ∧
  (vasyuninBEntryFormula 32 47 ≤ ((31224537291969483249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 32 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log32 := prim_log_32_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_32_47_bounds
  have b_Vkh := cotangentSumVFormula_47_32_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_32_lower, prim_log_32_upper] at b_log32
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_32_47_lower, cotangentSumVFormula_32_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_32_lower, cotangentSumVFormula_47_32_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_33_47_unfold :
    cotangentSumVFormula 33 47 =
      ((33/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 33 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_33_47_lower : ℚ := 1932638265107316743417 / 879609302220800000000
def cotangentSumVFormula_33_47_upper : ℚ := 1932638282700147319083 / 879609302220800000000
theorem cotangentSumVFormula_33_47_bounds :
  ((cotangentSumVFormula_33_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 47 ∧
  cotangentSumVFormula 33 47 ≤ ((cotangentSumVFormula_33_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_47_unfold]
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
  rw [cotangentSumVFormula_33_47_lower, cotangentSumVFormula_33_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_33_unfold :
    cotangentSumVFormula 47 33 =
      ((14/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((13/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((17/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((7/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((2/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((16/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((10/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((5/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_47_33_lower : ℚ := 2330542822901233877459 / 1759218604441600000000
def cotangentSumVFormula_47_33_upper : ℚ := 2330542858086144247541 / 1759218604441600000000
theorem cotangentSumVFormula_47_33_bounds :
  ((cotangentSumVFormula_47_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 33 ∧
  cotangentSumVFormula 47 33 ≤ ((cotangentSumVFormula_47_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_33_unfold]
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
  rw [cotangentSumVFormula_47_33_lower, cotangentSumVFormula_47_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3347_formula_bound :
  (((123165792072078895129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 47) ∧
  (vasyuninBEntryFormula 33 47 ≤ ((123174799271338667371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_33_47_bounds
  have b_Vkh := cotangentSumVFormula_47_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_33_47_lower, cotangentSumVFormula_33_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_33_lower, cotangentSumVFormula_47_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_34_47_unfold :
    cotangentSumVFormula 34 47 =
      ((34/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 34 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_34_47_lower : ℚ := 2104150697206537473271 / 439804651110400000000
def cotangentSumVFormula_34_47_upper : ℚ := 2104150706002946901729 / 439804651110400000000
theorem cotangentSumVFormula_34_47_bounds :
  ((cotangentSumVFormula_34_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 34 47 ∧
  cotangentSumVFormula 34 47 ≤ ((cotangentSumVFormula_34_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_34_47_unfold]
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
  rw [cotangentSumVFormula_34_47_lower, cotangentSumVFormula_34_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_34_unfold :
    cotangentSumVFormula 47 34 =
      ((13/34 : ℚ) : ℝ) * cotangentTermV 1 34    + 
      ((26/34 : ℚ) : ℝ) * cotangentTermV 2 34    + 
      ((5/34 : ℚ) : ℝ) * cotangentTermV 3 34    + 
      ((18/34 : ℚ) : ℝ) * cotangentTermV 4 34    + 
      ((31/34 : ℚ) : ℝ) * cotangentTermV 5 34    + 
      ((10/34 : ℚ) : ℝ) * cotangentTermV 6 34    + 
      ((23/34 : ℚ) : ℝ) * cotangentTermV 7 34    + 
      ((2/34 : ℚ) : ℝ) * cotangentTermV 8 34    + 
      ((15/34 : ℚ) : ℝ) * cotangentTermV 9 34    + 
      ((28/34 : ℚ) : ℝ) * cotangentTermV 10 34    + 
      ((7/34 : ℚ) : ℝ) * cotangentTermV 11 34    + 
      ((20/34 : ℚ) : ℝ) * cotangentTermV 12 34    + 
      ((33/34 : ℚ) : ℝ) * cotangentTermV 13 34    + 
      ((12/34 : ℚ) : ℝ) * cotangentTermV 14 34    + 
      ((25/34 : ℚ) : ℝ) * cotangentTermV 15 34    + 
      ((4/34 : ℚ) : ℝ) * cotangentTermV 16 34    + 
      ((17/34 : ℚ) : ℝ) * cotangentTermV 17 34    + 
      ((30/34 : ℚ) : ℝ) * cotangentTermV 18 34    + 
      ((9/34 : ℚ) : ℝ) * cotangentTermV 19 34    + 
      ((22/34 : ℚ) : ℝ) * cotangentTermV 20 34    + 
      ((1/34 : ℚ) : ℝ) * cotangentTermV 21 34    + 
      ((14/34 : ℚ) : ℝ) * cotangentTermV 22 34    + 
      ((27/34 : ℚ) : ℝ) * cotangentTermV 23 34    + 
      ((6/34 : ℚ) : ℝ) * cotangentTermV 24 34    + 
      ((19/34 : ℚ) : ℝ) * cotangentTermV 25 34    + 
      ((32/34 : ℚ) : ℝ) * cotangentTermV 26 34    + 
      ((11/34 : ℚ) : ℝ) * cotangentTermV 27 34    + 
      ((24/34 : ℚ) : ℝ) * cotangentTermV 28 34    + 
      ((3/34 : ℚ) : ℝ) * cotangentTermV 29 34    + 
      ((16/34 : ℚ) : ℝ) * cotangentTermV 30 34    + 
      ((29/34 : ℚ) : ℝ) * cotangentTermV 31 34    + 
      ((8/34 : ℚ) : ℝ) * cotangentTermV 32 34    + 
      ((21/34 : ℚ) : ℝ) * cotangentTermV 33 34 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_34]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((13/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((26/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((5/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((18/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((31/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((10/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((23/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((2/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((15/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((28/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((7/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((20/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((33/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((12/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((25/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((4/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((17/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((30/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((9/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((22/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((1/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((14/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((27/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((6/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((19/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((32/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((11/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((24/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((3/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((16/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((29/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((8/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((21/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33]
  try ring

def cotangentSumVFormula_47_34_lower : ℚ := -2013962235449161435041 / 1759218604441600000000
def cotangentSumVFormula_47_34_upper : ℚ := -2013962200264154189959 / 1759218604441600000000
theorem cotangentSumVFormula_47_34_bounds :
  ((cotangentSumVFormula_47_34_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 34 ∧
  cotangentSumVFormula 47 34 ≤ ((cotangentSumVFormula_47_34_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_34_unfold]
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
  rw [cotangentSumVFormula_47_34_lower, cotangentSumVFormula_47_34_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3447_formula_bound :
  (((60922163888127111627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 34 47) ∧
  (vasyuninBEntryFormula 34 47 ≤ ((7615833435969632531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 34 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log34 := prim_log_34_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_34_47_bounds
  have b_Vkh := cotangentSumVFormula_47_34_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_34_lower, prim_log_34_upper] at b_log34
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_34_47_lower, cotangentSumVFormula_34_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_34_lower, cotangentSumVFormula_47_34_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_35_47_unfold :
    cotangentSumVFormula 35 47 =
      ((35/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 35 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_35_47_lower : ℚ := 35947530019807058507 / 3435973836800000000
def cotangentSumVFormula_35_47_upper : ℚ := 575160481416462454513 / 54975581388800000000
theorem cotangentSumVFormula_35_47_bounds :
  ((cotangentSumVFormula_35_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 47 ∧
  cotangentSumVFormula 35 47 ≤ ((cotangentSumVFormula_35_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_47_unfold]
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
  rw [cotangentSumVFormula_35_47_lower, cotangentSumVFormula_35_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_35_unfold :
    cotangentSumVFormula 47 35 =
      ((12/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_47_35_lower : ℚ := -1495465745775679114927 / 219902325555200000000
def cotangentSumVFormula_47_35_upper : ℚ := -1495465741377546666323 / 219902325555200000000
theorem cotangentSumVFormula_47_35_bounds :
  ((cotangentSumVFormula_47_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 35 ∧
  cotangentSumVFormula 47 35 ≤ ((cotangentSumVFormula_47_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_35_unfold]
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
  rw [cotangentSumVFormula_47_35_lower, cotangentSumVFormula_47_35_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3547_formula_bound :
  (((60456618744538892877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 35 47) ∧
  (vasyuninBEntryFormula 35 47 ≤ ((15115280586042186937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 35 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log35 := prim_log_35_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_35_47_bounds
  have b_Vkh := cotangentSumVFormula_47_35_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_35_47_lower, cotangentSumVFormula_35_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_35_lower, cotangentSumVFormula_47_35_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_36_47_unfold :
    cotangentSumVFormula 36 47 =
      ((36/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 36 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_36_47_lower : ℚ := 557040349084467669099 / 109951162777600000000
def cotangentSumVFormula_36_47_upper : ℚ := 557040351283568268401 / 109951162777600000000
theorem cotangentSumVFormula_36_47_bounds :
  ((cotangentSumVFormula_36_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 47 ∧
  cotangentSumVFormula 36 47 ≤ ((cotangentSumVFormula_36_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_47_unfold]
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
  rw [cotangentSumVFormula_36_47_lower, cotangentSumVFormula_36_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_36_unfold :
    cotangentSumVFormula 47 36 =
      ((11/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_47_36_lower : ℚ := -2343335633971156747541 / 1759218604441600000000
def cotangentSumVFormula_47_36_upper : ℚ := -2343335598785974502459 / 1759218604441600000000
theorem cotangentSumVFormula_47_36_bounds :
  ((cotangentSumVFormula_47_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 36 ∧
  cotangentSumVFormula 47 36 ≤ ((cotangentSumVFormula_47_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_36_unfold]
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
  rw [cotangentSumVFormula_47_36_lower, cotangentSumVFormula_47_36_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3647_formula_bound :
  (((29933232708595391751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 36 47) ∧
  (vasyuninBEntryFormula 36 47 ≤ ((14967742254205186937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 36 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log36 := prim_log_36_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_36_47_bounds
  have b_Vkh := cotangentSumVFormula_47_36_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_36_47_lower, cotangentSumVFormula_36_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_36_lower, cotangentSumVFormula_47_36_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_47_unfold :
    cotangentSumVFormula 37 47 =
      ((37/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 37 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_37_47_lower : ℚ := 440038119656633639237 / 54975581388800000000
def cotangentSumVFormula_37_47_upper : ℚ := 110009530189045594097 / 13743895347200000000
theorem cotangentSumVFormula_37_47_bounds :
  ((cotangentSumVFormula_37_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 47 ∧
  cotangentSumVFormula 37 47 ≤ ((cotangentSumVFormula_37_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_47_unfold]
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
  rw [cotangentSumVFormula_37_47_lower, cotangentSumVFormula_37_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_37_unfold :
    cotangentSumVFormula 47 37 =
      ((10/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_47_37_lower : ℚ := -937107918655807239927 / 219902325555200000000
def cotangentSumVFormula_47_37_upper : ℚ := -937107914257676353823 / 219902325555200000000
theorem cotangentSumVFormula_47_37_bounds :
  ((cotangentSumVFormula_47_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 37 ∧
  cotangentSumVFormula 47 37 ≤ ((cotangentSumVFormula_47_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_37_unfold]
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
  rw [cotangentSumVFormula_47_37_lower, cotangentSumVFormula_47_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3747_formula_bound :
  (((118794435396720488879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 47) ∧
  (vasyuninBEntryFormula 37 47 ≤ ((118803442595979792371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_37_47_bounds
  have b_Vkh := cotangentSumVFormula_47_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_37_47_lower, cotangentSumVFormula_37_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_37_lower, cotangentSumVFormula_47_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_38_47_unfold :
    cotangentSumVFormula 38 47 =
      ((38/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 38 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_38_47_lower : ℚ := 3251228880056603098271 / 439804651110400000000
def cotangentSumVFormula_38_47_upper : ℚ := 3251228888852989089229 / 439804651110400000000
theorem cotangentSumVFormula_38_47_bounds :
  ((cotangentSumVFormula_38_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 47 ∧
  cotangentSumVFormula 38 47 ≤ ((cotangentSumVFormula_38_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_47_unfold]
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
  rw [cotangentSumVFormula_38_47_lower, cotangentSumVFormula_38_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_38_unfold :
    cotangentSumVFormula 47 38 =
      ((9/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((5/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_47_38_lower : ℚ := -406355987628275299651 / 109951162777600000000
def cotangentSumVFormula_47_38_upper : ℚ := -812711970858391197573 / 219902325555200000000
theorem cotangentSumVFormula_47_38_bounds :
  ((cotangentSumVFormula_47_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 38 ∧
  cotangentSumVFormula 47 38 ≤ ((cotangentSumVFormula_47_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_38_unfold]
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
  rw [cotangentSumVFormula_47_38_lower, cotangentSumVFormula_47_38_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3847_formula_bound :
  (((59022256502135892877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 38 47) ∧
  (vasyuninBEntryFormula 38 47 ≤ ((14756690025441436937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 38 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log38 := prim_log_38_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_38_47_bounds
  have b_Vkh := cotangentSumVFormula_47_38_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_38_47_lower, cotangentSumVFormula_38_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_38_lower, cotangentSumVFormula_47_38_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_39_47_unfold :
    cotangentSumVFormula 39 47 =
      ((39/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 39 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_39_47_lower : ℚ := 693018540664764889237 / 54975581388800000000
def cotangentSumVFormula_39_47_upper : ℚ := 693018541764312454513 / 54975581388800000000
theorem cotangentSumVFormula_39_47_bounds :
  ((cotangentSumVFormula_39_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 47 ∧
  cotangentSumVFormula 39 47 ≤ ((cotangentSumVFormula_39_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_47_unfold]
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
  rw [cotangentSumVFormula_39_47_lower, cotangentSumVFormula_39_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_39_unfold :
    cotangentSumVFormula 47 39 =
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
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_47_39_lower : ℚ := -494406505933667142013 / 54975581388800000000
def cotangentSumVFormula_47_39_upper : ℚ := -988813009668252825349 / 109951162777600000000
theorem cotangentSumVFormula_47_39_bounds :
  ((cotangentSumVFormula_47_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 39 ∧
  cotangentSumVFormula 47 39 ≤ ((cotangentSumVFormula_47_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_39_unfold]
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
  rw [cotangentSumVFormula_47_39_lower, cotangentSumVFormula_47_39_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3947_formula_bound :
  (((117406600231018113879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 39 47) ∧
  (vasyuninBEntryFormula 39 47 ≤ ((117415607430277729871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 39 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log39 := prim_log_39_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_39_47_bounds
  have b_Vkh := cotangentSumVFormula_47_39_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_39_47_lower, cotangentSumVFormula_39_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_39_lower, cotangentSumVFormula_47_39_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_40_47_unfold :
    cotangentSumVFormula 40 47 =
      ((40/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 40 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_40_47_lower : ℚ := 2738058182694752135073 / 219902325555200000000
def cotangentSumVFormula_40_47_upper : ℚ := 2738058187092936927427 / 219902325555200000000
theorem cotangentSumVFormula_40_47_bounds :
  ((cotangentSumVFormula_40_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 47 ∧
  cotangentSumVFormula 40 47 ≤ ((cotangentSumVFormula_40_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_47_unfold]
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
  rw [cotangentSumVFormula_40_47_lower, cotangentSumVFormula_40_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_40_unfold :
    cotangentSumVFormula 47 40 =
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
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_47_40_lower : ℚ := -1970432548507843958677 / 219902325555200000000
def cotangentSumVFormula_47_40_upper : ℚ := -1970432544109676353823 / 219902325555200000000
theorem cotangentSumVFormula_47_40_bounds :
  ((cotangentSumVFormula_47_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 40 ∧
  cotangentSumVFormula 47 40 ≤ ((cotangentSumVFormula_47_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_40_unfold]
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
  rw [cotangentSumVFormula_47_40_lower, cotangentSumVFormula_47_40_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4047_formula_bound :
  (((14609504645006438063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 40 47) ∧
  (vasyuninBEntryFormula 40 47 ≤ ((58442522179655482123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 40 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log40 := prim_log_40_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_40_47_bounds
  have b_Vkh := cotangentSumVFormula_47_40_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_40_47_lower, cotangentSumVFormula_40_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_40_lower, cotangentSumVFormula_47_40_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_47_unfold :
    cotangentSumVFormula 41 47 =
      ((41/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 41 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_41_47_lower : ℚ := 3340742676749072447573 / 219902325555200000000
def cotangentSumVFormula_41_47_upper : ℚ := 3340742681147259583677 / 219902325555200000000
theorem cotangentSumVFormula_41_47_bounds :
  ((cotangentSumVFormula_41_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 47 ∧
  cotangentSumVFormula 41 47 ≤ ((cotangentSumVFormula_41_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_47_unfold]
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
  rw [cotangentSumVFormula_41_47_lower, cotangentSumVFormula_41_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_41_unfold :
    cotangentSumVFormula 47 41 =
      ((6/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((1/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((2/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((8/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((3/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((9/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((4/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((5/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_47_41_lower : ℚ := -2613731852822111146177 / 219902325555200000000
def cotangentSumVFormula_47_41_upper : ℚ := -2613731848423953697573 / 219902325555200000000
theorem cotangentSumVFormula_47_41_bounds :
  ((cotangentSumVFormula_47_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 41 ∧
  cotangentSumVFormula 47 41 ≤ ((cotangentSumVFormula_47_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_41_unfold]
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
  rw [cotangentSumVFormula_47_41_lower, cotangentSumVFormula_47_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4147_formula_bound :
  (((116538054254762957629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 47) ∧
  (vasyuninBEntryFormula 41 47 ≤ ((116547061454022167371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_41_47_bounds
  have b_Vkh := cotangentSumVFormula_47_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_41_47_lower, cotangentSumVFormula_41_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_41_lower, cotangentSumVFormula_47_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_42_47_unfold :
    cotangentSumVFormula 42 47 =
      ((42/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 42 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_42_47_lower : ℚ := 1776999595765826262849 / 109951162777600000000
def cotangentSumVFormula_42_47_upper : ℚ := 1776999597964923737151 / 109951162777600000000
theorem cotangentSumVFormula_42_47_bounds :
  ((cotangentSumVFormula_42_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 47 ∧
  cotangentSumVFormula 42 47 ≤ ((cotangentSumVFormula_42_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_47_unfold]
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
  rw [cotangentSumVFormula_42_47_lower, cotangentSumVFormula_42_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_42_unfold :
    cotangentSumVFormula 47 42 =
      ((5/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((1/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 47 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_47_42_lower : ℚ := -2880029973381054896177 / 219902325555200000000
def cotangentSumVFormula_47_42_upper : ℚ := -2880029968982849791323 / 219902325555200000000
theorem cotangentSumVFormula_47_42_bounds :
  ((cotangentSumVFormula_47_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 42 ∧
  cotangentSumVFormula 47 42 ≤ ((cotangentSumVFormula_47_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_42_unfold]
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
  rw [cotangentSumVFormula_47_42_lower, cotangentSumVFormula_47_42_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4247_formula_bound :
  (((58179476870016611627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 42 47) ∧
  (vasyuninBEntryFormula 42 47 ≤ ((14545995117411655687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 42 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log42 := prim_log_42_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_42_47_bounds
  have b_Vkh := cotangentSumVFormula_47_42_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_42_47_lower, cotangentSumVFormula_42_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_42_lower, cotangentSumVFormula_47_42_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_43_47_unfold :
    cotangentSumVFormula 43 47 =
      ((43/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 43 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_43_47_lower : ℚ := 2173699101558809075349 / 109951162777600000000
def cotangentSumVFormula_43_47_upper : ℚ := 2173699103757911237151 / 109951162777600000000
theorem cotangentSumVFormula_43_47_bounds :
  ((cotangentSumVFormula_43_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 47 ∧
  cotangentSumVFormula 43 47 ≤ ((cotangentSumVFormula_43_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_47_unfold]
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
  rw [cotangentSumVFormula_43_47_lower, cotangentSumVFormula_43_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_43_unfold :
    cotangentSumVFormula 47 43 =
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
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 47 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_47_43_lower : ℚ := -1871354990201078424651 / 109951162777600000000
def cotangentSumVFormula_47_43_upper : ℚ := -1871354988001965325349 / 109951162777600000000
theorem cotangentSumVFormula_47_43_bounds :
  ((cotangentSumVFormula_47_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 43 ∧
  cotangentSumVFormula 47 43 ≤ ((cotangentSumVFormula_47_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_43_unfold]
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
  rw [cotangentSumVFormula_47_43_lower, cotangentSumVFormula_47_43_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4347_formula_bound :
  (((116390452848279363879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 43 47) ∧
  (vasyuninBEntryFormula 43 47 ≤ ((116399460047539761121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 43 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log43 := log_43_certified_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_43_47_bounds
  have b_Vkh := cotangentSumVFormula_47_43_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_43_47_lower, cotangentSumVFormula_43_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_43_lower, cotangentSumVFormula_47_43_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_44_47_unfold :
    cotangentSumVFormula 44 47 =
      ((44/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 44 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_44_47_lower : ℚ := 644547954766885764931 / 27487790694400000000
def cotangentSumVFormula_44_47_upper : ℚ := 644547955316661891319 / 27487790694400000000
theorem cotangentSumVFormula_44_47_bounds :
  ((cotangentSumVFormula_44_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 47 ∧
  cotangentSumVFormula 44 47 ≤ ((cotangentSumVFormula_44_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_47_unfold]
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
  rw [cotangentSumVFormula_44_47_lower, cotangentSumVFormula_44_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_44_unfold :
    cotangentSumVFormula 47 44 =
      ((3/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 47 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_47_44_lower : ℚ := -290007635017090125347 / 13743895347200000000
def cotangentSumVFormula_47_44_upper : ℚ := -1160030538968800826737 / 54975581388800000000
theorem cotangentSumVFormula_47_44_bounds :
  ((cotangentSumVFormula_47_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 44 ∧
  cotangentSumVFormula 47 44 ≤ ((cotangentSumVFormula_47_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_44_unfold]
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
  rw [cotangentSumVFormula_47_44_lower, cotangentSumVFormula_47_44_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4447_formula_bound :
  (((116665341524298551379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 44 47) ∧
  (vasyuninBEntryFormula 44 47 ≤ ((116674348723559073621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 44 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log44 := prim_log_44_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_44_47_bounds
  have b_Vkh := cotangentSumVFormula_47_44_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_44_47_lower, cotangentSumVFormula_44_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_44_lower, cotangentSumVFormula_47_44_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_45_47_unfold :
    cotangentSumVFormula 45 47 =
      ((45/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((46/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 45 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_45_47_lower : ℚ := 398655353791308312153 / 13743895347200000000
def cotangentSumVFormula_45_47_upper : ℚ := 797310708132392360069 / 27487790694400000000
theorem cotangentSumVFormula_45_47_bounds :
  ((cotangentSumVFormula_45_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 45 47 ∧
  cotangentSumVFormula 45 47 ≤ ((cotangentSumVFormula_45_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_45_47_unfold]
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
  rw [cotangentSumVFormula_45_47_lower, cotangentSumVFormula_45_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_45_unfold :
    cotangentSumVFormula 47 45 =
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
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((2/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((4/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((6/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((8/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((10/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((12/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((14/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((16/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((18/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((20/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((22/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((24/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((26/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((28/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((30/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((32/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((34/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((36/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((38/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((40/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((42/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((44/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((1/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((3/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((5/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((7/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((9/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((11/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((13/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((15/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((17/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((19/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((21/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((23/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((25/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((27/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((29/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((31/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((33/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((35/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((37/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((39/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((41/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 47 : ℕ) : ℝ) / ((45 : ℕ) : ℝ)) = ((43/45 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44]
  try ring

def cotangentSumVFormula_47_45_lower : ℚ := -2988013905592582330901 / 109951162777600000000
def cotangentSumVFormula_47_45_upper : ℚ := -2988013903393457512849 / 109951162777600000000
theorem cotangentSumVFormula_47_45_bounds :
  ((cotangentSumVFormula_47_45_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 45 ∧
  cotangentSumVFormula 47 45 ≤ ((cotangentSumVFormula_47_45_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_45_unfold]
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
  rw [cotangentSumVFormula_47_45_lower, cotangentSumVFormula_47_45_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4547_formula_bound :
  (((117263951271919926379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 45 47) ∧
  (vasyuninBEntryFormula 45 47 ≤ ((117272958471180479871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 45 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log45 := prim_log_45_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_45_47_bounds
  have b_Vkh := cotangentSumVFormula_47_45_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_45_lower, prim_log_45_upper] at b_log45
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_45_47_lower, cotangentSumVFormula_45_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_45_lower, cotangentSumVFormula_47_45_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_46_47_unfold :
    cotangentSumVFormula 46 47 =
      ((46/47 : ℚ) : ℝ) * cotangentTermV 1 47    + 
      ((45/47 : ℚ) : ℝ) * cotangentTermV 2 47    + 
      ((44/47 : ℚ) : ℝ) * cotangentTermV 3 47    + 
      ((43/47 : ℚ) : ℝ) * cotangentTermV 4 47    + 
      ((42/47 : ℚ) : ℝ) * cotangentTermV 5 47    + 
      ((41/47 : ℚ) : ℝ) * cotangentTermV 6 47    + 
      ((40/47 : ℚ) : ℝ) * cotangentTermV 7 47    + 
      ((39/47 : ℚ) : ℝ) * cotangentTermV 8 47    + 
      ((38/47 : ℚ) : ℝ) * cotangentTermV 9 47    + 
      ((37/47 : ℚ) : ℝ) * cotangentTermV 10 47    + 
      ((36/47 : ℚ) : ℝ) * cotangentTermV 11 47    + 
      ((35/47 : ℚ) : ℝ) * cotangentTermV 12 47    + 
      ((34/47 : ℚ) : ℝ) * cotangentTermV 13 47    + 
      ((33/47 : ℚ) : ℝ) * cotangentTermV 14 47    + 
      ((32/47 : ℚ) : ℝ) * cotangentTermV 15 47    + 
      ((31/47 : ℚ) : ℝ) * cotangentTermV 16 47    + 
      ((30/47 : ℚ) : ℝ) * cotangentTermV 17 47    + 
      ((29/47 : ℚ) : ℝ) * cotangentTermV 18 47    + 
      ((28/47 : ℚ) : ℝ) * cotangentTermV 19 47    + 
      ((27/47 : ℚ) : ℝ) * cotangentTermV 20 47    + 
      ((26/47 : ℚ) : ℝ) * cotangentTermV 21 47    + 
      ((25/47 : ℚ) : ℝ) * cotangentTermV 22 47    + 
      ((24/47 : ℚ) : ℝ) * cotangentTermV 23 47    + 
      ((23/47 : ℚ) : ℝ) * cotangentTermV 24 47    + 
      ((22/47 : ℚ) : ℝ) * cotangentTermV 25 47    + 
      ((21/47 : ℚ) : ℝ) * cotangentTermV 26 47    + 
      ((20/47 : ℚ) : ℝ) * cotangentTermV 27 47    + 
      ((19/47 : ℚ) : ℝ) * cotangentTermV 28 47    + 
      ((18/47 : ℚ) : ℝ) * cotangentTermV 29 47    + 
      ((17/47 : ℚ) : ℝ) * cotangentTermV 30 47    + 
      ((16/47 : ℚ) : ℝ) * cotangentTermV 31 47    + 
      ((15/47 : ℚ) : ℝ) * cotangentTermV 32 47    + 
      ((14/47 : ℚ) : ℝ) * cotangentTermV 33 47    + 
      ((13/47 : ℚ) : ℝ) * cotangentTermV 34 47    + 
      ((12/47 : ℚ) : ℝ) * cotangentTermV 35 47    + 
      ((11/47 : ℚ) : ℝ) * cotangentTermV 36 47    + 
      ((10/47 : ℚ) : ℝ) * cotangentTermV 37 47    + 
      ((9/47 : ℚ) : ℝ) * cotangentTermV 38 47    + 
      ((8/47 : ℚ) : ℝ) * cotangentTermV 39 47    + 
      ((7/47 : ℚ) : ℝ) * cotangentTermV 40 47    + 
      ((6/47 : ℚ) : ℝ) * cotangentTermV 41 47    + 
      ((5/47 : ℚ) : ℝ) * cotangentTermV 42 47    + 
      ((4/47 : ℚ) : ℝ) * cotangentTermV 43 47    + 
      ((3/47 : ℚ) : ℝ) * cotangentTermV 44 47    + 
      ((2/47 : ℚ) : ℝ) * cotangentTermV 45 47    + 
      ((1/47 : ℚ) : ℝ) * cotangentTermV 46 47 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_47]
  have hf_1 : Int.fract (((1 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((46/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((45/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((44/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((43/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((42/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((41/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((40/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((39/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((38/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((37/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((36/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((35/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((34/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((33/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((32/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((31/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((30/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((29/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((28/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((27/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((26/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((25/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((24/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((23/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((22/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((21/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((20/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((19/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((18/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((17/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((16/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((15/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((14/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((13/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((12/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((11/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((10/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((9/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((8/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((7/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((6/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((5/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((4/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((3/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((2/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 46 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = ((1/47 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46]
  try ring

def cotangentSumVFormula_46_47_lower : ℚ := 1073682512609889671181 / 27487790694400000000
def cotangentSumVFormula_46_47_upper : ℚ := 1073682513159666578819 / 27487790694400000000
theorem cotangentSumVFormula_46_47_bounds :
  ((cotangentSumVFormula_46_47_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 46 47 ∧
  cotangentSumVFormula 46 47 ≤ ((cotangentSumVFormula_46_47_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_46_47_unfold]
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
  rw [cotangentSumVFormula_46_47_lower, cotangentSumVFormula_46_47_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_47_46_unfold :
    cotangentSumVFormula 47 46 =
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
  have hf_1 : Int.fract (((1 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((1/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((2/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((3/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((4/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((5/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((6/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((7/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((8/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((9/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((10/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((11/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((12/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((13/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((14/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((15/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((16/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((17/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((18/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((19/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((20/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((21/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((22/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((23/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((24/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((25/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((26/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((27/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((28/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((29/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((30/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((31/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((32/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((33/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((34/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((35/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((36/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((37/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((38/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((39/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((40/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((41/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((42/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((43/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((44/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 47 : ℕ) : ℝ) / ((46 : ℕ) : ℝ)) = ((45/46 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45]
  try ring

def cotangentSumVFormula_47_46_lower : ℚ := -2084741350160439798263 / 54975581388800000000
def cotangentSumVFormula_47_46_upper : ℚ := -2084741349060875045487 / 54975581388800000000
theorem cotangentSumVFormula_47_46_bounds :
  ((cotangentSumVFormula_47_46_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 47 46 ∧
  cotangentSumVFormula 47 46 ≤ ((cotangentSumVFormula_47_46_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_47_46_unfold]
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
  rw [cotangentSumVFormula_47_46_lower, cotangentSumVFormula_47_46_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4647_formula_bound :
  (((118357009663645832629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 46 47) ∧
  (vasyuninBEntryFormula 46 47 ≤ ((118366016862906511121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 46 47 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log46 := prim_log_46_bounds
  have b_log47 := log_47_certified_bounds
  have b_Vhk := cotangentSumVFormula_46_47_bounds
  have b_Vkh := cotangentSumVFormula_47_46_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_46_lower, prim_log_46_upper] at b_log46
  simp only [log_47_lower, log_47_upper] at b_log47
  simp only [cotangentSumVFormula_46_47_lower, cotangentSumVFormula_46_47_upper] at b_Vhk
  simp only [cotangentSumVFormula_47_46_lower, cotangentSumVFormula_47_46_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_48_unfold :
    cotangentSumVFormula 1 48 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((1/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((2/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((3/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((4/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((5/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((6/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((7/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((8/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((9/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((10/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((11/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((12/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((13/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((14/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((15/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((16/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((17/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((18/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((19/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((20/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((21/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((22/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((23/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((24/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((25/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((26/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((27/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((28/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((29/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((30/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((31/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((32/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((33/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((34/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((35/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((36/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((37/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((38/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((39/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((40/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((41/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((42/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((43/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((44/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((45/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((46/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 1 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((47/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47]
  try ring

def cotangentSumVFormula_1_48_lower : ℚ := -2210361147933589017013 / 54975581388800000000
def cotangentSumVFormula_1_48_upper : ℚ := -2210361146834032857987 / 54975581388800000000
theorem cotangentSumVFormula_1_48_bounds :
  ((cotangentSumVFormula_1_48_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 48 ∧
  cotangentSumVFormula 1 48 ≤ ((cotangentSumVFormula_1_48_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_48_unfold]
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
  rw [cotangentSumVFormula_1_48_lower, cotangentSumVFormula_1_48_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_48_1_unfold :
    cotangentSumVFormula 48 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_48_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_48_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_48_1_bounds :
  ((cotangentSumVFormula_48_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 48 1 ∧
  cotangentSumVFormula 48 1 ≤ ((cotangentSumVFormula_48_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_48_1_unfold]
  rw [cotangentSumVFormula_48_1_lower, cotangentSumVFormula_48_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_148_formula_bound :
  (((35990550585897375563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 48) ∧
  (vasyuninBEntryFormula 1 48 ≤ ((35991676485821374437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 48 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log48 := prim_log_48_bounds
  have b_Vhk := cotangentSumVFormula_1_48_bounds
  have b_Vkh := cotangentSumVFormula_48_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_48_lower, prim_log_48_upper] at b_log48
  simp only [cotangentSumVFormula_1_48_lower, cotangentSumVFormula_1_48_upper] at b_Vhk
  simp only [cotangentSumVFormula_48_1_lower, cotangentSumVFormula_48_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_48_unfold :
    cotangentSumVFormula 5 48 =
      ((5/48 : ℚ) : ℝ) * cotangentTermV 1 48    + 
      ((10/48 : ℚ) : ℝ) * cotangentTermV 2 48    + 
      ((15/48 : ℚ) : ℝ) * cotangentTermV 3 48    + 
      ((20/48 : ℚ) : ℝ) * cotangentTermV 4 48    + 
      ((25/48 : ℚ) : ℝ) * cotangentTermV 5 48    + 
      ((30/48 : ℚ) : ℝ) * cotangentTermV 6 48    + 
      ((35/48 : ℚ) : ℝ) * cotangentTermV 7 48    + 
      ((40/48 : ℚ) : ℝ) * cotangentTermV 8 48    + 
      ((45/48 : ℚ) : ℝ) * cotangentTermV 9 48    + 
      ((2/48 : ℚ) : ℝ) * cotangentTermV 10 48    + 
      ((7/48 : ℚ) : ℝ) * cotangentTermV 11 48    + 
      ((12/48 : ℚ) : ℝ) * cotangentTermV 12 48    + 
      ((17/48 : ℚ) : ℝ) * cotangentTermV 13 48    + 
      ((22/48 : ℚ) : ℝ) * cotangentTermV 14 48    + 
      ((27/48 : ℚ) : ℝ) * cotangentTermV 15 48    + 
      ((32/48 : ℚ) : ℝ) * cotangentTermV 16 48    + 
      ((37/48 : ℚ) : ℝ) * cotangentTermV 17 48    + 
      ((42/48 : ℚ) : ℝ) * cotangentTermV 18 48    + 
      ((47/48 : ℚ) : ℝ) * cotangentTermV 19 48    + 
      ((4/48 : ℚ) : ℝ) * cotangentTermV 20 48    + 
      ((9/48 : ℚ) : ℝ) * cotangentTermV 21 48    + 
      ((14/48 : ℚ) : ℝ) * cotangentTermV 22 48    + 
      ((19/48 : ℚ) : ℝ) * cotangentTermV 23 48    + 
      ((24/48 : ℚ) : ℝ) * cotangentTermV 24 48    + 
      ((29/48 : ℚ) : ℝ) * cotangentTermV 25 48    + 
      ((34/48 : ℚ) : ℝ) * cotangentTermV 26 48    + 
      ((39/48 : ℚ) : ℝ) * cotangentTermV 27 48    + 
      ((44/48 : ℚ) : ℝ) * cotangentTermV 28 48    + 
      ((1/48 : ℚ) : ℝ) * cotangentTermV 29 48    + 
      ((6/48 : ℚ) : ℝ) * cotangentTermV 30 48    + 
      ((11/48 : ℚ) : ℝ) * cotangentTermV 31 48    + 
      ((16/48 : ℚ) : ℝ) * cotangentTermV 32 48    + 
      ((21/48 : ℚ) : ℝ) * cotangentTermV 33 48    + 
      ((26/48 : ℚ) : ℝ) * cotangentTermV 34 48    + 
      ((31/48 : ℚ) : ℝ) * cotangentTermV 35 48    + 
      ((36/48 : ℚ) : ℝ) * cotangentTermV 36 48    + 
      ((41/48 : ℚ) : ℝ) * cotangentTermV 37 48    + 
      ((46/48 : ℚ) : ℝ) * cotangentTermV 38 48    + 
      ((3/48 : ℚ) : ℝ) * cotangentTermV 39 48    + 
      ((8/48 : ℚ) : ℝ) * cotangentTermV 40 48    + 
      ((13/48 : ℚ) : ℝ) * cotangentTermV 41 48    + 
      ((18/48 : ℚ) : ℝ) * cotangentTermV 42 48    + 
      ((23/48 : ℚ) : ℝ) * cotangentTermV 43 48    + 
      ((28/48 : ℚ) : ℝ) * cotangentTermV 44 48    + 
      ((33/48 : ℚ) : ℝ) * cotangentTermV 45 48    + 
      ((38/48 : ℚ) : ℝ) * cotangentTermV 46 48    + 
      ((43/48 : ℚ) : ℝ) * cotangentTermV 47 48 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_48]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((5/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((10/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((15/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((20/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((25/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((30/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((35/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((40/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((45/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((2/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((7/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((12/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((17/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((22/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((27/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((32/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((37/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((42/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((47/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((4/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((9/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((14/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((19/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((24/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((29/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((34/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((39/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((44/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((1/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((6/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((11/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((16/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((21/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((26/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((31/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((36/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((41/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((46/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((3/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((8/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((13/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((18/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((23/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((28/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((33/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((38/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 5 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((43/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47]
  try ring

def cotangentSumVFormula_5_48_lower : ℚ := -932154294024645267013 / 54975581388800000000
def cotangentSumVFormula_5_48_upper : ℚ := -58259643307817996007 / 3435973836800000000
theorem cotangentSumVFormula_5_48_bounds :
  ((cotangentSumVFormula_5_48_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 48 ∧
  cotangentSumVFormula 5 48 ≤ ((cotangentSumVFormula_5_48_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_48_unfold]
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
  rw [cotangentSumVFormula_5_48_lower, cotangentSumVFormula_5_48_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_48_5_unfold :
    cotangentSumVFormula 48 5 =
      ((3/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 48 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 48 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 48 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 48 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_48_5_lower : ℚ := 2260935262917356492469 / 28147497671065600000000
def cotangentSumVFormula_48_5_upper : ℚ := 2260935825867424757531 / 28147497671065600000000
theorem cotangentSumVFormula_48_5_bounds :
  ((cotangentSumVFormula_48_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 48 5 ∧
  cotangentSumVFormula 48 5 ≤ ((cotangentSumVFormula_48_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_48_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_48_5_lower, cotangentSumVFormula_48_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_548_formula_bound :
  (((52951524007466516751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 48) ∧
  (vasyuninBEntryFormula 5 48 ≤ ((52953775807287014499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 48 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log48 := prim_log_48_bounds
  have b_Vhk := cotangentSumVFormula_5_48_bounds
  have b_Vkh := cotangentSumVFormula_48_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_48_lower, prim_log_48_upper] at b_log48
  simp only [cotangentSumVFormula_5_48_lower, cotangentSumVFormula_5_48_upper] at b_Vhk
  simp only [cotangentSumVFormula_48_5_lower, cotangentSumVFormula_48_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_48_unfold :
    cotangentSumVFormula 7 48 =
      ((7/48 : ℚ) : ℝ) * cotangentTermV 1 48    + 
      ((14/48 : ℚ) : ℝ) * cotangentTermV 2 48    + 
      ((21/48 : ℚ) : ℝ) * cotangentTermV 3 48    + 
      ((28/48 : ℚ) : ℝ) * cotangentTermV 4 48    + 
      ((35/48 : ℚ) : ℝ) * cotangentTermV 5 48    + 
      ((42/48 : ℚ) : ℝ) * cotangentTermV 6 48    + 
      ((1/48 : ℚ) : ℝ) * cotangentTermV 7 48    + 
      ((8/48 : ℚ) : ℝ) * cotangentTermV 8 48    + 
      ((15/48 : ℚ) : ℝ) * cotangentTermV 9 48    + 
      ((22/48 : ℚ) : ℝ) * cotangentTermV 10 48    + 
      ((29/48 : ℚ) : ℝ) * cotangentTermV 11 48    + 
      ((36/48 : ℚ) : ℝ) * cotangentTermV 12 48    + 
      ((43/48 : ℚ) : ℝ) * cotangentTermV 13 48    + 
      ((2/48 : ℚ) : ℝ) * cotangentTermV 14 48    + 
      ((9/48 : ℚ) : ℝ) * cotangentTermV 15 48    + 
      ((16/48 : ℚ) : ℝ) * cotangentTermV 16 48    + 
      ((23/48 : ℚ) : ℝ) * cotangentTermV 17 48    + 
      ((30/48 : ℚ) : ℝ) * cotangentTermV 18 48    + 
      ((37/48 : ℚ) : ℝ) * cotangentTermV 19 48    + 
      ((44/48 : ℚ) : ℝ) * cotangentTermV 20 48    + 
      ((3/48 : ℚ) : ℝ) * cotangentTermV 21 48    + 
      ((10/48 : ℚ) : ℝ) * cotangentTermV 22 48    + 
      ((17/48 : ℚ) : ℝ) * cotangentTermV 23 48    + 
      ((24/48 : ℚ) : ℝ) * cotangentTermV 24 48    + 
      ((31/48 : ℚ) : ℝ) * cotangentTermV 25 48    + 
      ((38/48 : ℚ) : ℝ) * cotangentTermV 26 48    + 
      ((45/48 : ℚ) : ℝ) * cotangentTermV 27 48    + 
      ((4/48 : ℚ) : ℝ) * cotangentTermV 28 48    + 
      ((11/48 : ℚ) : ℝ) * cotangentTermV 29 48    + 
      ((18/48 : ℚ) : ℝ) * cotangentTermV 30 48    + 
      ((25/48 : ℚ) : ℝ) * cotangentTermV 31 48    + 
      ((32/48 : ℚ) : ℝ) * cotangentTermV 32 48    + 
      ((39/48 : ℚ) : ℝ) * cotangentTermV 33 48    + 
      ((46/48 : ℚ) : ℝ) * cotangentTermV 34 48    + 
      ((5/48 : ℚ) : ℝ) * cotangentTermV 35 48    + 
      ((12/48 : ℚ) : ℝ) * cotangentTermV 36 48    + 
      ((19/48 : ℚ) : ℝ) * cotangentTermV 37 48    + 
      ((26/48 : ℚ) : ℝ) * cotangentTermV 38 48    + 
      ((33/48 : ℚ) : ℝ) * cotangentTermV 39 48    + 
      ((40/48 : ℚ) : ℝ) * cotangentTermV 40 48    + 
      ((47/48 : ℚ) : ℝ) * cotangentTermV 41 48    + 
      ((6/48 : ℚ) : ℝ) * cotangentTermV 42 48    + 
      ((13/48 : ℚ) : ℝ) * cotangentTermV 43 48    + 
      ((20/48 : ℚ) : ℝ) * cotangentTermV 44 48    + 
      ((27/48 : ℚ) : ℝ) * cotangentTermV 45 48    + 
      ((34/48 : ℚ) : ℝ) * cotangentTermV 46 48    + 
      ((41/48 : ℚ) : ℝ) * cotangentTermV 47 48 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_48]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((7/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((14/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((21/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((28/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((35/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((42/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((1/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((8/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((15/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((22/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((29/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((36/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((43/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((2/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((9/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((16/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((23/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((30/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((37/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((44/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((3/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((10/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((17/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((24/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((31/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((38/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((45/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((4/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((11/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((18/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((25/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((32/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((39/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((46/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((5/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((12/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((19/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((26/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((33/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((40/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((47/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((6/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((13/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((20/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((27/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((34/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 7 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((41/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47]
  try ring

def cotangentSumVFormula_7_48_lower : ℚ := -1566448226600197174651 / 109951162777600000000
def cotangentSumVFormula_7_48_upper : ℚ := -1566448224401084075349 / 109951162777600000000
theorem cotangentSumVFormula_7_48_bounds :
  ((cotangentSumVFormula_7_48_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 48 ∧
  cotangentSumVFormula 7 48 ≤ ((cotangentSumVFormula_7_48_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_48_unfold]
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
  rw [cotangentSumVFormula_7_48_lower, cotangentSumVFormula_7_48_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_48_7_unfold :
    cotangentSumVFormula 48 7 =
      ((6/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 48 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 48 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 48 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 48 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 48 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 48 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_48_7_lower : ℚ := 1633971105500482368417 / 879609302220800000000
def cotangentSumVFormula_48_7_upper : ℚ := 1633971123092677006583 / 879609302220800000000
theorem cotangentSumVFormula_48_7_bounds :
  ((cotangentSumVFormula_48_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 48 7 ∧
  cotangentSumVFormula 48 7 ≤ ((cotangentSumVFormula_48_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_48_7_unfold]
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
  rw [cotangentSumVFormula_48_7_lower, cotangentSumVFormula_48_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_748_formula_bound :
  (((24562422479625625563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 48) ∧
  (vasyuninBEntryFormula 7 48 ≤ ((49127096759069670749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 48 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log48 := prim_log_48_bounds
  have b_Vhk := cotangentSumVFormula_7_48_bounds
  have b_Vkh := cotangentSumVFormula_48_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_48_lower, prim_log_48_upper] at b_log48
  simp only [cotangentSumVFormula_7_48_lower, cotangentSumVFormula_7_48_upper] at b_Vhk
  simp only [cotangentSumVFormula_48_7_lower, cotangentSumVFormula_48_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_48_unfold :
    cotangentSumVFormula 11 48 =
      ((11/48 : ℚ) : ℝ) * cotangentTermV 1 48    + 
      ((22/48 : ℚ) : ℝ) * cotangentTermV 2 48    + 
      ((33/48 : ℚ) : ℝ) * cotangentTermV 3 48    + 
      ((44/48 : ℚ) : ℝ) * cotangentTermV 4 48    + 
      ((7/48 : ℚ) : ℝ) * cotangentTermV 5 48    + 
      ((18/48 : ℚ) : ℝ) * cotangentTermV 6 48    + 
      ((29/48 : ℚ) : ℝ) * cotangentTermV 7 48    + 
      ((40/48 : ℚ) : ℝ) * cotangentTermV 8 48    + 
      ((3/48 : ℚ) : ℝ) * cotangentTermV 9 48    + 
      ((14/48 : ℚ) : ℝ) * cotangentTermV 10 48    + 
      ((25/48 : ℚ) : ℝ) * cotangentTermV 11 48    + 
      ((36/48 : ℚ) : ℝ) * cotangentTermV 12 48    + 
      ((47/48 : ℚ) : ℝ) * cotangentTermV 13 48    + 
      ((10/48 : ℚ) : ℝ) * cotangentTermV 14 48    + 
      ((21/48 : ℚ) : ℝ) * cotangentTermV 15 48    + 
      ((32/48 : ℚ) : ℝ) * cotangentTermV 16 48    + 
      ((43/48 : ℚ) : ℝ) * cotangentTermV 17 48    + 
      ((6/48 : ℚ) : ℝ) * cotangentTermV 18 48    + 
      ((17/48 : ℚ) : ℝ) * cotangentTermV 19 48    + 
      ((28/48 : ℚ) : ℝ) * cotangentTermV 20 48    + 
      ((39/48 : ℚ) : ℝ) * cotangentTermV 21 48    + 
      ((2/48 : ℚ) : ℝ) * cotangentTermV 22 48    + 
      ((13/48 : ℚ) : ℝ) * cotangentTermV 23 48    + 
      ((24/48 : ℚ) : ℝ) * cotangentTermV 24 48    + 
      ((35/48 : ℚ) : ℝ) * cotangentTermV 25 48    + 
      ((46/48 : ℚ) : ℝ) * cotangentTermV 26 48    + 
      ((9/48 : ℚ) : ℝ) * cotangentTermV 27 48    + 
      ((20/48 : ℚ) : ℝ) * cotangentTermV 28 48    + 
      ((31/48 : ℚ) : ℝ) * cotangentTermV 29 48    + 
      ((42/48 : ℚ) : ℝ) * cotangentTermV 30 48    + 
      ((5/48 : ℚ) : ℝ) * cotangentTermV 31 48    + 
      ((16/48 : ℚ) : ℝ) * cotangentTermV 32 48    + 
      ((27/48 : ℚ) : ℝ) * cotangentTermV 33 48    + 
      ((38/48 : ℚ) : ℝ) * cotangentTermV 34 48    + 
      ((1/48 : ℚ) : ℝ) * cotangentTermV 35 48    + 
      ((12/48 : ℚ) : ℝ) * cotangentTermV 36 48    + 
      ((23/48 : ℚ) : ℝ) * cotangentTermV 37 48    + 
      ((34/48 : ℚ) : ℝ) * cotangentTermV 38 48    + 
      ((45/48 : ℚ) : ℝ) * cotangentTermV 39 48    + 
      ((8/48 : ℚ) : ℝ) * cotangentTermV 40 48    + 
      ((19/48 : ℚ) : ℝ) * cotangentTermV 41 48    + 
      ((30/48 : ℚ) : ℝ) * cotangentTermV 42 48    + 
      ((41/48 : ℚ) : ℝ) * cotangentTermV 43 48    + 
      ((4/48 : ℚ) : ℝ) * cotangentTermV 44 48    + 
      ((15/48 : ℚ) : ℝ) * cotangentTermV 45 48    + 
      ((26/48 : ℚ) : ℝ) * cotangentTermV 46 48    + 
      ((37/48 : ℚ) : ℝ) * cotangentTermV 47 48 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_48]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((11/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((22/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((33/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((44/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((7/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((18/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((29/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((40/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((3/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((14/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((25/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((36/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((47/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((10/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((21/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((32/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((43/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((6/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((17/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((28/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((39/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((2/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((13/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((24/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((35/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((46/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((9/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((20/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((31/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((42/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((5/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((16/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((27/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((38/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((1/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((12/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((23/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((34/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((45/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((8/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((19/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((30/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((41/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_44 : Int.fract (((44 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((4/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_45 : Int.fract (((45 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((15/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_46 : Int.fract (((46 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((26/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_47 : Int.fract (((47 * 11 : ℕ) : ℝ) / ((48 : ℕ) : ℝ)) = ((37/48 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43, hf_44, hf_45, hf_46, hf_47]
  try ring

def cotangentSumVFormula_11_48_lower : ℚ := -2559344635865482839229 / 439804651110400000000
def cotangentSumVFormula_11_48_upper : ℚ := -2559344627069040598271 / 439804651110400000000
theorem cotangentSumVFormula_11_48_bounds :
  ((cotangentSumVFormula_11_48_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 48 ∧
  cotangentSumVFormula 11 48 ≤ ((cotangentSumVFormula_11_48_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_48_unfold]
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
  rw [cotangentSumVFormula_11_48_lower, cotangentSumVFormula_11_48_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_48_11_unfold :
    cotangentSumVFormula 48 11 =
      ((4/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 48 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_48_11_lower : ℚ := -3098045053564121698207 / 3518437208883200000000
def cotangentSumVFormula_48_11_upper : ℚ := -3098044983195265801793 / 3518437208883200000000
theorem cotangentSumVFormula_48_11_bounds :
  ((cotangentSumVFormula_48_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 48 11 ∧
  cotangentSumVFormula 48 11 ≤ ((cotangentSumVFormula_48_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_48_11_unfold]
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
  rw [cotangentSumVFormula_48_11_lower, cotangentSumVFormula_48_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1148_formula_bound :
  (((21810939295995313063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 48) ∧
  (vasyuninBEntryFormula 11 48 ≤ ((43624130391807326999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 48 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log48 := prim_log_48_bounds
  have b_Vhk := cotangentSumVFormula_11_48_bounds
  have b_Vkh := cotangentSumVFormula_48_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_48_lower, prim_log_48_upper] at b_log48
  simp only [cotangentSumVFormula_11_48_lower, cotangentSumVFormula_11_48_upper] at b_Vhk
  simp only [cotangentSumVFormula_48_11_lower, cotangentSumVFormula_48_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
