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

theorem cotangentSumVFormula_33_43_unfold :
    cotangentSumVFormula 33 43 =
      ((33/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 33 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_33_43_lower : ℚ := 2325251568609181223271 / 439804651110400000000
def cotangentSumVFormula_33_43_upper : ℚ := 2325251577405525026729 / 439804651110400000000
theorem cotangentSumVFormula_33_43_bounds :
  ((cotangentSumVFormula_33_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 43 ∧
  cotangentSumVFormula 33 43 ≤ ((cotangentSumVFormula_33_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_43_unfold]
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
  rw [cotangentSumVFormula_33_43_lower, cotangentSumVFormula_33_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_33_unfold :
    cotangentSumVFormula 43 33 =
      ((10/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((7/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((17/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((14/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((5/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((2/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((16/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((13/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_43_33_lower : ℚ := -3285193799082354403791 / 1759218604441600000000
def cotangentSumVFormula_43_33_upper : ℚ := -3285193763897442471209 / 1759218604441600000000
theorem cotangentSumVFormula_43_33_bounds :
  ((cotangentSumVFormula_43_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 33 ∧
  cotangentSumVFormula 43 33 ≤ ((cotangentSumVFormula_43_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_33_unfold]
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
  rw [cotangentSumVFormula_43_33_lower, cotangentSumVFormula_43_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3343_formula_bound :
  (((32696931955362423001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 43) ∧
  (vasyuninBEntryFormula 33 43 ≤ ((32699183755177295749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_33_43_bounds
  have b_Vkh := cotangentSumVFormula_43_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_33_43_lower, cotangentSumVFormula_33_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_33_lower, cotangentSumVFormula_43_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_34_43_unfold :
    cotangentSumVFormula 34 43 =
      ((34/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 34 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_34_43_lower : ℚ := 915369858762989544099 / 109951162777600000000
def cotangentSumVFormula_34_43_upper : ℚ := 915369860962075299651 / 109951162777600000000
theorem cotangentSumVFormula_34_43_bounds :
  ((cotangentSumVFormula_34_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 34 43 ∧
  cotangentSumVFormula 34 43 ≤ ((cotangentSumVFormula_34_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_34_43_unfold]
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
  rw [cotangentSumVFormula_34_43_lower, cotangentSumVFormula_34_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_34_unfold :
    cotangentSumVFormula 43 34 =
      ((9/34 : ℚ) : ℝ) * cotangentTermV 1 34    + 
      ((18/34 : ℚ) : ℝ) * cotangentTermV 2 34    + 
      ((27/34 : ℚ) : ℝ) * cotangentTermV 3 34    + 
      ((2/34 : ℚ) : ℝ) * cotangentTermV 4 34    + 
      ((11/34 : ℚ) : ℝ) * cotangentTermV 5 34    + 
      ((20/34 : ℚ) : ℝ) * cotangentTermV 6 34    + 
      ((29/34 : ℚ) : ℝ) * cotangentTermV 7 34    + 
      ((4/34 : ℚ) : ℝ) * cotangentTermV 8 34    + 
      ((13/34 : ℚ) : ℝ) * cotangentTermV 9 34    + 
      ((22/34 : ℚ) : ℝ) * cotangentTermV 10 34    + 
      ((31/34 : ℚ) : ℝ) * cotangentTermV 11 34    + 
      ((6/34 : ℚ) : ℝ) * cotangentTermV 12 34    + 
      ((15/34 : ℚ) : ℝ) * cotangentTermV 13 34    + 
      ((24/34 : ℚ) : ℝ) * cotangentTermV 14 34    + 
      ((33/34 : ℚ) : ℝ) * cotangentTermV 15 34    + 
      ((8/34 : ℚ) : ℝ) * cotangentTermV 16 34    + 
      ((17/34 : ℚ) : ℝ) * cotangentTermV 17 34    + 
      ((26/34 : ℚ) : ℝ) * cotangentTermV 18 34    + 
      ((1/34 : ℚ) : ℝ) * cotangentTermV 19 34    + 
      ((10/34 : ℚ) : ℝ) * cotangentTermV 20 34    + 
      ((19/34 : ℚ) : ℝ) * cotangentTermV 21 34    + 
      ((28/34 : ℚ) : ℝ) * cotangentTermV 22 34    + 
      ((3/34 : ℚ) : ℝ) * cotangentTermV 23 34    + 
      ((12/34 : ℚ) : ℝ) * cotangentTermV 24 34    + 
      ((21/34 : ℚ) : ℝ) * cotangentTermV 25 34    + 
      ((30/34 : ℚ) : ℝ) * cotangentTermV 26 34    + 
      ((5/34 : ℚ) : ℝ) * cotangentTermV 27 34    + 
      ((14/34 : ℚ) : ℝ) * cotangentTermV 28 34    + 
      ((23/34 : ℚ) : ℝ) * cotangentTermV 29 34    + 
      ((32/34 : ℚ) : ℝ) * cotangentTermV 30 34    + 
      ((7/34 : ℚ) : ℝ) * cotangentTermV 31 34    + 
      ((16/34 : ℚ) : ℝ) * cotangentTermV 32 34    + 
      ((25/34 : ℚ) : ℝ) * cotangentTermV 33 34 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_34]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((9/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((18/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((27/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((2/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((11/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((20/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((29/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((4/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((13/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((22/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((31/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((6/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((15/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((24/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((33/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((8/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((17/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((26/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((1/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((10/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((19/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((28/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((3/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((12/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((21/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((30/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((5/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((14/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((23/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((32/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((7/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((16/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((25/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33]
  try ring

def cotangentSumVFormula_43_34_lower : ℚ := -2158594899977761745479 / 439804651110400000000
def cotangentSumVFormula_43_34_upper : ℚ := -2158594891181493723271 / 439804651110400000000
theorem cotangentSumVFormula_43_34_bounds :
  ((cotangentSumVFormula_43_34_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 34 ∧
  cotangentSumVFormula 43 34 ≤ ((cotangentSumVFormula_43_34_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_34_unfold]
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
  rw [cotangentSumVFormula_43_34_lower, cotangentSumVFormula_43_34_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3443_formula_bound :
  (((64857926836530236627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 34 43) ∧
  (vasyuninBEntryFormula 34 43 ≤ ((16215607609040030687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 34 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log34 := prim_log_34_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_34_43_bounds
  have b_Vkh := cotangentSumVFormula_43_34_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_34_lower, prim_log_34_upper] at b_log34
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_34_43_lower, cotangentSumVFormula_34_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_34_lower, cotangentSumVFormula_43_34_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_35_43_unfold :
    cotangentSumVFormula 35 43 =
      ((35/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 35 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_35_43_lower : ℚ := 3458903535933524973271 / 439804651110400000000
def cotangentSumVFormula_35_43_upper : ℚ := 3458903544729864089229 / 439804651110400000000
theorem cotangentSumVFormula_35_43_bounds :
  ((cotangentSumVFormula_35_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 43 ∧
  cotangentSumVFormula 35 43 ≤ ((cotangentSumVFormula_35_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_43_unfold]
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
  rw [cotangentSumVFormula_35_43_lower, cotangentSumVFormula_35_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_35_unfold :
    cotangentSumVFormula 43 35 =
      ((8/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_43_35_lower : ℚ := -493932590461231549651 / 109951162777600000000
def cotangentSumVFormula_43_35_upper : ℚ := -987865176524322447573 / 219902325555200000000
theorem cotangentSumVFormula_43_35_bounds :
  ((cotangentSumVFormula_43_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 35 ∧
  cotangentSumVFormula 43 35 ≤ ((cotangentSumVFormula_43_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_35_unfold]
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
  rw [cotangentSumVFormula_43_35_lower, cotangentSumVFormula_43_35_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3543_formula_bound :
  (((64402392908667642877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 35 43) ∧
  (vasyuninBEntryFormula 35 43 ≤ ((32203448254148764499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 35 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log35 := prim_log_35_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_35_43_bounds
  have b_Vkh := cotangentSumVFormula_43_35_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_35_43_lower, cotangentSumVFormula_35_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_35_lower, cotangentSumVFormula_43_35_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_36_43_unfold :
    cotangentSumVFormula 36 43 =
      ((36/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 36 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_36_43_lower : ℚ := 1753167904360926353823 / 219902325555200000000
def cotangentSumVFormula_36_43_upper : ℚ := 109572994297443250347 / 13743895347200000000
theorem cotangentSumVFormula_36_43_bounds :
  ((cotangentSumVFormula_36_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 43 ∧
  cotangentSumVFormula 36 43 ≤ ((cotangentSumVFormula_36_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_43_unfold]
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
  rw [cotangentSumVFormula_36_43_lower, cotangentSumVFormula_36_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_36_unfold :
    cotangentSumVFormula 43 36 =
      ((7/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_43_36_lower : ℚ := -2068423204082095339229 / 439804651110400000000
def cotangentSumVFormula_43_36_upper : ℚ := -2068423195285799973271 / 439804651110400000000
theorem cotangentSumVFormula_43_36_bounds :
  ((cotangentSumVFormula_43_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 36 ∧
  cotangentSumVFormula 43 36 ≤ ((cotangentSumVFormula_43_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_36_unfold]
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
  rw [cotangentSumVFormula_43_36_lower, cotangentSumVFormula_43_36_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3643_formula_bound :
  (((128117160303789082629 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 36 43) ∧
  (vasyuninBEntryFormula 36 43 ≤ ((128126167503048761121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 36 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log36 := prim_log_36_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_36_43_bounds
  have b_Vkh := cotangentSumVFormula_43_36_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_36_43_lower, cotangentSumVFormula_36_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_36_lower, cotangentSumVFormula_43_36_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_37_43_unfold :
    cotangentSumVFormula 37 43 =
      ((37/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 37 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_37_43_lower : ℚ := 1128857131462216106599 / 109951162777600000000
def cotangentSumVFormula_37_43_upper : ℚ := 282214283415324391319 / 27487790694400000000
theorem cotangentSumVFormula_37_43_bounds :
  ((cotangentSumVFormula_37_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 43 ∧
  cotangentSumVFormula 37 43 ≤ ((cotangentSumVFormula_37_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_43_unfold]
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
  rw [cotangentSumVFormula_37_43_lower, cotangentSumVFormula_37_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_37_unfold :
    cotangentSumVFormula 43 37 =
      ((6/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_43_37_lower : ℚ := -3141951301369710182979 / 439804651110400000000
def cotangentSumVFormula_43_37_upper : ℚ := -3141951292573434348271 / 439804651110400000000
theorem cotangentSumVFormula_43_37_bounds :
  ((cotangentSumVFormula_43_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 37 ∧
  cotangentSumVFormula 43 37 ≤ ((cotangentSumVFormula_43_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_37_unfold]
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
  rw [cotangentSumVFormula_43_37_lower, cotangentSumVFormula_43_37_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3743_formula_bound :
  (((127574262870458926379 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 37 43) ∧
  (vasyuninBEntryFormula 37 43 ≤ ((127583270069718261121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 37 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log37 := log_37_certified_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_37_43_bounds
  have b_Vkh := cotangentSumVFormula_43_37_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_37_43_lower, cotangentSumVFormula_37_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_37_lower, cotangentSumVFormula_43_37_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_38_43_unfold :
    cotangentSumVFormula 38 43 =
      ((38/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 38 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_38_43_lower : ℚ := 3046850690644649010073 / 219902325555200000000
def cotangentSumVFormula_38_43_upper : ℚ := 3046850695042807239927 / 219902325555200000000
theorem cotangentSumVFormula_38_43_bounds :
  ((cotangentSumVFormula_38_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 38 43 ∧
  cotangentSumVFormula 38 43 ≤ ((cotangentSumVFormula_38_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_38_43_unfold]
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
  rw [cotangentSumVFormula_38_43_lower, cotangentSumVFormula_38_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_38_unfold :
    cotangentSumVFormula 43 38 =
      ((5/38 : ℚ) : ℝ) * cotangentTermV 1 38    + 
      ((10/38 : ℚ) : ℝ) * cotangentTermV 2 38    + 
      ((15/38 : ℚ) : ℝ) * cotangentTermV 3 38    + 
      ((20/38 : ℚ) : ℝ) * cotangentTermV 4 38    + 
      ((25/38 : ℚ) : ℝ) * cotangentTermV 5 38    + 
      ((30/38 : ℚ) : ℝ) * cotangentTermV 6 38    + 
      ((35/38 : ℚ) : ℝ) * cotangentTermV 7 38    + 
      ((2/38 : ℚ) : ℝ) * cotangentTermV 8 38    + 
      ((7/38 : ℚ) : ℝ) * cotangentTermV 9 38    + 
      ((12/38 : ℚ) : ℝ) * cotangentTermV 10 38    + 
      ((17/38 : ℚ) : ℝ) * cotangentTermV 11 38    + 
      ((22/38 : ℚ) : ℝ) * cotangentTermV 12 38    + 
      ((27/38 : ℚ) : ℝ) * cotangentTermV 13 38    + 
      ((32/38 : ℚ) : ℝ) * cotangentTermV 14 38    + 
      ((37/38 : ℚ) : ℝ) * cotangentTermV 15 38    + 
      ((4/38 : ℚ) : ℝ) * cotangentTermV 16 38    + 
      ((9/38 : ℚ) : ℝ) * cotangentTermV 17 38    + 
      ((14/38 : ℚ) : ℝ) * cotangentTermV 18 38    + 
      ((19/38 : ℚ) : ℝ) * cotangentTermV 19 38    + 
      ((24/38 : ℚ) : ℝ) * cotangentTermV 20 38    + 
      ((29/38 : ℚ) : ℝ) * cotangentTermV 21 38    + 
      ((34/38 : ℚ) : ℝ) * cotangentTermV 22 38    + 
      ((1/38 : ℚ) : ℝ) * cotangentTermV 23 38    + 
      ((6/38 : ℚ) : ℝ) * cotangentTermV 24 38    + 
      ((11/38 : ℚ) : ℝ) * cotangentTermV 25 38    + 
      ((16/38 : ℚ) : ℝ) * cotangentTermV 26 38    + 
      ((21/38 : ℚ) : ℝ) * cotangentTermV 27 38    + 
      ((26/38 : ℚ) : ℝ) * cotangentTermV 28 38    + 
      ((31/38 : ℚ) : ℝ) * cotangentTermV 29 38    + 
      ((36/38 : ℚ) : ℝ) * cotangentTermV 30 38    + 
      ((3/38 : ℚ) : ℝ) * cotangentTermV 31 38    + 
      ((8/38 : ℚ) : ℝ) * cotangentTermV 32 38    + 
      ((13/38 : ℚ) : ℝ) * cotangentTermV 33 38    + 
      ((18/38 : ℚ) : ℝ) * cotangentTermV 34 38    + 
      ((23/38 : ℚ) : ℝ) * cotangentTermV 35 38    + 
      ((28/38 : ℚ) : ℝ) * cotangentTermV 36 38    + 
      ((33/38 : ℚ) : ℝ) * cotangentTermV 37 38 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_38]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((5/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((10/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((15/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((20/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((25/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((30/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((35/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((2/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((7/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((12/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((17/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((22/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((27/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((32/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((37/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((4/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((9/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((14/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((19/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((24/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((29/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((34/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((1/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((6/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((11/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((16/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((21/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((26/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((31/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((36/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((3/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((8/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((13/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((18/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((23/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((28/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((38 : ℕ) : ℝ)) = ((33/38 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37]
  try ring

def cotangentSumVFormula_43_38_lower : ℚ := -2405790479927290833677 / 219902325555200000000
def cotangentSumVFormula_43_38_upper : ℚ := -2405790475529128697573 / 219902325555200000000
theorem cotangentSumVFormula_43_38_bounds :
  ((cotangentSumVFormula_43_38_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 38 ∧
  cotangentSumVFormula 43 38 ≤ ((cotangentSumVFormula_43_38_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_38_unfold]
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
  rw [cotangentSumVFormula_43_38_lower, cotangentSumVFormula_43_38_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3843_formula_bound :
  (((127244399569698770129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 38 43) ∧
  (vasyuninBEntryFormula 38 43 ≤ ((127253406768958229871 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 38 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log38 := prim_log_38_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_38_43_bounds
  have b_Vkh := cotangentSumVFormula_43_38_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_38_lower, prim_log_38_upper] at b_log38
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_38_43_lower, cotangentSumVFormula_38_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_38_lower, cotangentSumVFormula_43_38_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_39_43_unfold :
    cotangentSumVFormula 39 43 =
      ((39/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 39 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_39_43_lower : ℚ := 1871354988001998137849 / 109951162777600000000
def cotangentSumVFormula_39_43_upper : ℚ := 1871354990201074518401 / 109951162777600000000
theorem cotangentSumVFormula_39_43_bounds :
  ((cotangentSumVFormula_39_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 39 43 ∧
  cotangentSumVFormula 39 43 ≤ ((cotangentSumVFormula_39_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_39_43_unfold]
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
  rw [cotangentSumVFormula_39_43_lower, cotangentSumVFormula_39_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_39_unfold :
    cotangentSumVFormula 43 39 =
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
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((4/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((8/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((12/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((16/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((20/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((24/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((28/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((32/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((36/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((1/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((5/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((9/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((13/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((17/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((21/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((25/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((29/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((33/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((37/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((2/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((6/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((10/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((14/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((18/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((22/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((26/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((30/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((34/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((38/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((3/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((7/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((11/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((15/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((19/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((23/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((27/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((31/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((39 : ℕ) : ℝ)) = ((35/39 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38]
  try ring

def cotangentSumVFormula_43_39_lower : ℚ := -791021376373308548263 / 54975581388800000000
def cotangentSumVFormula_43_39_upper : ℚ := -1582042750547530950349 / 109951162777600000000
theorem cotangentSumVFormula_43_39_bounds :
  ((cotangentSumVFormula_43_39_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 39 ∧
  cotangentSumVFormula 43 39 ≤ ((cotangentSumVFormula_43_39_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_39_unfold]
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
  rw [cotangentSumVFormula_43_39_lower, cotangentSumVFormula_43_39_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3943_formula_bound :
  (((127177569876287270129 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 39 43) ∧
  (vasyuninBEntryFormula 39 43 ≤ ((127186577075546761121 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 39 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log39 := prim_log_39_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_39_43_bounds
  have b_Vkh := cotangentSumVFormula_43_39_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_39_lower, prim_log_39_upper] at b_log39
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_39_43_lower, cotangentSumVFormula_39_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_39_lower, cotangentSumVFormula_43_39_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_40_43_unfold :
    cotangentSumVFormula 40 43 =
      ((40/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 40 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_40_43_lower : ℚ := 2193286430461074700349 / 109951162777600000000
def cotangentSumVFormula_40_43_upper : ℚ := 2193286432660149518401 / 109951162777600000000
theorem cotangentSumVFormula_40_43_bounds :
  ((cotangentSumVFormula_40_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 40 43 ∧
  cotangentSumVFormula 40 43 ≤ ((cotangentSumVFormula_40_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_40_43_unfold]
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
  rw [cotangentSumVFormula_40_43_lower, cotangentSumVFormula_40_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_40_unfold :
    cotangentSumVFormula 43 40 =
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
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((3/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((6/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((9/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((12/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((15/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((18/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((21/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((24/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((27/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((30/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((33/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((36/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((39/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((2/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((5/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((8/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((11/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((14/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((17/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((20/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((23/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((26/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((29/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((32/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((35/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((38/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((1/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((4/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((7/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((10/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((13/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((16/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((19/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((22/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((25/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((28/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((31/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((34/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((40 : ℕ) : ℝ)) = ((37/40 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39]
  try ring

def cotangentSumVFormula_43_40_lower : ℚ := -1944819489503094830901 / 109951162777600000000
def cotangentSumVFormula_43_40_upper : ℚ := -1944819487304005950349 / 109951162777600000000
theorem cotangentSumVFormula_43_40_bounds :
  ((cotangentSumVFormula_43_40_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 40 ∧
  cotangentSumVFormula 43 40 ≤ ((cotangentSumVFormula_43_40_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_40_unfold]
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
  rw [cotangentSumVFormula_43_40_lower, cotangentSumVFormula_43_40_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4043_formula_bound :
  (((127403616926134488879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 40 43) ∧
  (vasyuninBEntryFormula 40 43 ≤ ((127412624125393917371 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 40 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log40 := prim_log_40_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_40_43_bounds
  have b_Vkh := cotangentSumVFormula_43_40_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_40_lower, prim_log_40_upper] at b_log40
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_40_43_lower, cotangentSumVFormula_40_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_40_lower, cotangentSumVFormula_43_40_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_41_43_unfold :
    cotangentSumVFormula 41 43 =
      ((41/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((42/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 41 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_41_43_lower : ℚ := 2789896562959013762849 / 109951162777600000000
def cotangentSumVFormula_41_43_upper : ℚ := 2789896565158102643401 / 109951162777600000000
theorem cotangentSumVFormula_41_43_bounds :
  ((cotangentSumVFormula_41_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 41 43 ∧
  cotangentSumVFormula 41 43 ≤ ((cotangentSumVFormula_41_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_41_43_unfold]
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
  rw [cotangentSumVFormula_41_43_lower, cotangentSumVFormula_41_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_41_unfold :
    cotangentSumVFormula 43 41 =
      ((2/41 : ℚ) : ℝ) * cotangentTermV 1 41    + 
      ((4/41 : ℚ) : ℝ) * cotangentTermV 2 41    + 
      ((6/41 : ℚ) : ℝ) * cotangentTermV 3 41    + 
      ((8/41 : ℚ) : ℝ) * cotangentTermV 4 41    + 
      ((10/41 : ℚ) : ℝ) * cotangentTermV 5 41    + 
      ((12/41 : ℚ) : ℝ) * cotangentTermV 6 41    + 
      ((14/41 : ℚ) : ℝ) * cotangentTermV 7 41    + 
      ((16/41 : ℚ) : ℝ) * cotangentTermV 8 41    + 
      ((18/41 : ℚ) : ℝ) * cotangentTermV 9 41    + 
      ((20/41 : ℚ) : ℝ) * cotangentTermV 10 41    + 
      ((22/41 : ℚ) : ℝ) * cotangentTermV 11 41    + 
      ((24/41 : ℚ) : ℝ) * cotangentTermV 12 41    + 
      ((26/41 : ℚ) : ℝ) * cotangentTermV 13 41    + 
      ((28/41 : ℚ) : ℝ) * cotangentTermV 14 41    + 
      ((30/41 : ℚ) : ℝ) * cotangentTermV 15 41    + 
      ((32/41 : ℚ) : ℝ) * cotangentTermV 16 41    + 
      ((34/41 : ℚ) : ℝ) * cotangentTermV 17 41    + 
      ((36/41 : ℚ) : ℝ) * cotangentTermV 18 41    + 
      ((38/41 : ℚ) : ℝ) * cotangentTermV 19 41    + 
      ((40/41 : ℚ) : ℝ) * cotangentTermV 20 41    + 
      ((1/41 : ℚ) : ℝ) * cotangentTermV 21 41    + 
      ((3/41 : ℚ) : ℝ) * cotangentTermV 22 41    + 
      ((5/41 : ℚ) : ℝ) * cotangentTermV 23 41    + 
      ((7/41 : ℚ) : ℝ) * cotangentTermV 24 41    + 
      ((9/41 : ℚ) : ℝ) * cotangentTermV 25 41    + 
      ((11/41 : ℚ) : ℝ) * cotangentTermV 26 41    + 
      ((13/41 : ℚ) : ℝ) * cotangentTermV 27 41    + 
      ((15/41 : ℚ) : ℝ) * cotangentTermV 28 41    + 
      ((17/41 : ℚ) : ℝ) * cotangentTermV 29 41    + 
      ((19/41 : ℚ) : ℝ) * cotangentTermV 30 41    + 
      ((21/41 : ℚ) : ℝ) * cotangentTermV 31 41    + 
      ((23/41 : ℚ) : ℝ) * cotangentTermV 32 41    + 
      ((25/41 : ℚ) : ℝ) * cotangentTermV 33 41    + 
      ((27/41 : ℚ) : ℝ) * cotangentTermV 34 41    + 
      ((29/41 : ℚ) : ℝ) * cotangentTermV 35 41    + 
      ((31/41 : ℚ) : ℝ) * cotangentTermV 36 41    + 
      ((33/41 : ℚ) : ℝ) * cotangentTermV 37 41    + 
      ((35/41 : ℚ) : ℝ) * cotangentTermV 38 41    + 
      ((37/41 : ℚ) : ℝ) * cotangentTermV 39 41    + 
      ((39/41 : ℚ) : ℝ) * cotangentTermV 40 41 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_41]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((2/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((4/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((6/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((8/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((10/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((12/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((14/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((16/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((18/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((20/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((22/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((24/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((26/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((28/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((30/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((32/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((34/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((36/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((38/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((40/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((1/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((3/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((5/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((7/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((9/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((11/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((13/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((15/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((17/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((19/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((21/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((23/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((25/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((27/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((29/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((31/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((33/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((35/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((37/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((41 : ℕ) : ℝ)) = ((39/41 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40]
  try ring

def cotangentSumVFormula_43_41_lower : ℚ := -648758899164975953819 / 27487790694400000000
def cotangentSumVFormula_43_41_upper : ℚ := -1297517797230411764237 / 54975581388800000000
theorem cotangentSumVFormula_43_41_bounds :
  ((cotangentSumVFormula_43_41_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 41 ∧
  cotangentSumVFormula 43 41 ≤ ((cotangentSumVFormula_43_41_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_41_unfold]
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
  rw [cotangentSumVFormula_43_41_lower, cotangentSumVFormula_43_41_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4143_formula_bound :
  (((8001128775143054969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 41 43) ∧
  (vasyuninBEntryFormula 41 43 ≤ ((2000422931274193289 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 41 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log41 := log_41_certified_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_41_43_bounds
  have b_Vkh := cotangentSumVFormula_43_41_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_41_lower, log_41_upper] at b_log41
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_41_43_lower, cotangentSumVFormula_41_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_41_lower, cotangentSumVFormula_43_41_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_42_43_unfold :
    cotangentSumVFormula 42 43 =
      ((42/43 : ℚ) : ℝ) * cotangentTermV 1 43    + 
      ((41/43 : ℚ) : ℝ) * cotangentTermV 2 43    + 
      ((40/43 : ℚ) : ℝ) * cotangentTermV 3 43    + 
      ((39/43 : ℚ) : ℝ) * cotangentTermV 4 43    + 
      ((38/43 : ℚ) : ℝ) * cotangentTermV 5 43    + 
      ((37/43 : ℚ) : ℝ) * cotangentTermV 6 43    + 
      ((36/43 : ℚ) : ℝ) * cotangentTermV 7 43    + 
      ((35/43 : ℚ) : ℝ) * cotangentTermV 8 43    + 
      ((34/43 : ℚ) : ℝ) * cotangentTermV 9 43    + 
      ((33/43 : ℚ) : ℝ) * cotangentTermV 10 43    + 
      ((32/43 : ℚ) : ℝ) * cotangentTermV 11 43    + 
      ((31/43 : ℚ) : ℝ) * cotangentTermV 12 43    + 
      ((30/43 : ℚ) : ℝ) * cotangentTermV 13 43    + 
      ((29/43 : ℚ) : ℝ) * cotangentTermV 14 43    + 
      ((28/43 : ℚ) : ℝ) * cotangentTermV 15 43    + 
      ((27/43 : ℚ) : ℝ) * cotangentTermV 16 43    + 
      ((26/43 : ℚ) : ℝ) * cotangentTermV 17 43    + 
      ((25/43 : ℚ) : ℝ) * cotangentTermV 18 43    + 
      ((24/43 : ℚ) : ℝ) * cotangentTermV 19 43    + 
      ((23/43 : ℚ) : ℝ) * cotangentTermV 20 43    + 
      ((22/43 : ℚ) : ℝ) * cotangentTermV 21 43    + 
      ((21/43 : ℚ) : ℝ) * cotangentTermV 22 43    + 
      ((20/43 : ℚ) : ℝ) * cotangentTermV 23 43    + 
      ((19/43 : ℚ) : ℝ) * cotangentTermV 24 43    + 
      ((18/43 : ℚ) : ℝ) * cotangentTermV 25 43    + 
      ((17/43 : ℚ) : ℝ) * cotangentTermV 26 43    + 
      ((16/43 : ℚ) : ℝ) * cotangentTermV 27 43    + 
      ((15/43 : ℚ) : ℝ) * cotangentTermV 28 43    + 
      ((14/43 : ℚ) : ℝ) * cotangentTermV 29 43    + 
      ((13/43 : ℚ) : ℝ) * cotangentTermV 30 43    + 
      ((12/43 : ℚ) : ℝ) * cotangentTermV 31 43    + 
      ((11/43 : ℚ) : ℝ) * cotangentTermV 32 43    + 
      ((10/43 : ℚ) : ℝ) * cotangentTermV 33 43    + 
      ((9/43 : ℚ) : ℝ) * cotangentTermV 34 43    + 
      ((8/43 : ℚ) : ℝ) * cotangentTermV 35 43    + 
      ((7/43 : ℚ) : ℝ) * cotangentTermV 36 43    + 
      ((6/43 : ℚ) : ℝ) * cotangentTermV 37 43    + 
      ((5/43 : ℚ) : ℝ) * cotangentTermV 38 43    + 
      ((4/43 : ℚ) : ℝ) * cotangentTermV 39 43    + 
      ((3/43 : ℚ) : ℝ) * cotangentTermV 40 43    + 
      ((2/43 : ℚ) : ℝ) * cotangentTermV 41 43    + 
      ((1/43 : ℚ) : ℝ) * cotangentTermV 42 43 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_43]
  have hf_1 : Int.fract (((1 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((42/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((41/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((40/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((39/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((38/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((37/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((36/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((35/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((34/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((33/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((32/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((31/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((30/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((29/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((28/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((27/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((26/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((25/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((24/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((23/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((22/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((21/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((20/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((19/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((18/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((17/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((16/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((15/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((14/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((13/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((12/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((11/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((10/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((9/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((8/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((7/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((6/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((5/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((4/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((3/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((2/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 42 : ℕ) : ℝ) / ((43 : ℕ) : ℝ)) = ((1/43 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42]
  try ring

def cotangentSumVFormula_42_43_lower : ℚ := 1899187840798582076737 / 54975581388800000000
def cotangentSumVFormula_42_43_upper : ℚ := 1899187841898129642013 / 54975581388800000000
theorem cotangentSumVFormula_42_43_bounds :
  ((cotangentSumVFormula_42_43_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 42 43 ∧
  cotangentSumVFormula 42 43 ≤ ((cotangentSumVFormula_42_43_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_42_43_unfold]
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
  rw [cotangentSumVFormula_42_43_lower, cotangentSumVFormula_42_43_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_43_42_unfold :
    cotangentSumVFormula 43 42 =
      ((1/42 : ℚ) : ℝ) * cotangentTermV 1 42    + 
      ((2/42 : ℚ) : ℝ) * cotangentTermV 2 42    + 
      ((3/42 : ℚ) : ℝ) * cotangentTermV 3 42    + 
      ((4/42 : ℚ) : ℝ) * cotangentTermV 4 42    + 
      ((5/42 : ℚ) : ℝ) * cotangentTermV 5 42    + 
      ((6/42 : ℚ) : ℝ) * cotangentTermV 6 42    + 
      ((7/42 : ℚ) : ℝ) * cotangentTermV 7 42    + 
      ((8/42 : ℚ) : ℝ) * cotangentTermV 8 42    + 
      ((9/42 : ℚ) : ℝ) * cotangentTermV 9 42    + 
      ((10/42 : ℚ) : ℝ) * cotangentTermV 10 42    + 
      ((11/42 : ℚ) : ℝ) * cotangentTermV 11 42    + 
      ((12/42 : ℚ) : ℝ) * cotangentTermV 12 42    + 
      ((13/42 : ℚ) : ℝ) * cotangentTermV 13 42    + 
      ((14/42 : ℚ) : ℝ) * cotangentTermV 14 42    + 
      ((15/42 : ℚ) : ℝ) * cotangentTermV 15 42    + 
      ((16/42 : ℚ) : ℝ) * cotangentTermV 16 42    + 
      ((17/42 : ℚ) : ℝ) * cotangentTermV 17 42    + 
      ((18/42 : ℚ) : ℝ) * cotangentTermV 18 42    + 
      ((19/42 : ℚ) : ℝ) * cotangentTermV 19 42    + 
      ((20/42 : ℚ) : ℝ) * cotangentTermV 20 42    + 
      ((21/42 : ℚ) : ℝ) * cotangentTermV 21 42    + 
      ((22/42 : ℚ) : ℝ) * cotangentTermV 22 42    + 
      ((23/42 : ℚ) : ℝ) * cotangentTermV 23 42    + 
      ((24/42 : ℚ) : ℝ) * cotangentTermV 24 42    + 
      ((25/42 : ℚ) : ℝ) * cotangentTermV 25 42    + 
      ((26/42 : ℚ) : ℝ) * cotangentTermV 26 42    + 
      ((27/42 : ℚ) : ℝ) * cotangentTermV 27 42    + 
      ((28/42 : ℚ) : ℝ) * cotangentTermV 28 42    + 
      ((29/42 : ℚ) : ℝ) * cotangentTermV 29 42    + 
      ((30/42 : ℚ) : ℝ) * cotangentTermV 30 42    + 
      ((31/42 : ℚ) : ℝ) * cotangentTermV 31 42    + 
      ((32/42 : ℚ) : ℝ) * cotangentTermV 32 42    + 
      ((33/42 : ℚ) : ℝ) * cotangentTermV 33 42    + 
      ((34/42 : ℚ) : ℝ) * cotangentTermV 34 42    + 
      ((35/42 : ℚ) : ℝ) * cotangentTermV 35 42    + 
      ((36/42 : ℚ) : ℝ) * cotangentTermV 36 42    + 
      ((37/42 : ℚ) : ℝ) * cotangentTermV 37 42    + 
      ((38/42 : ℚ) : ℝ) * cotangentTermV 38 42    + 
      ((39/42 : ℚ) : ℝ) * cotangentTermV 39 42    + 
      ((40/42 : ℚ) : ℝ) * cotangentTermV 40 42    + 
      ((41/42 : ℚ) : ℝ) * cotangentTermV 41 42 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_42]
  have hf_1 : Int.fract (((1 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((1/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((2/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((3/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((4/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((5/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((6/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((7/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((8/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((9/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((10/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((11/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((12/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((13/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((14/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((15/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((16/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((17/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((18/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((19/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((20/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((21/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((22/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((23/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((24/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((25/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((26/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((27/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((28/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((29/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((30/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((31/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((32/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((33/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((34/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((35/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((36/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((37/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((38/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((39/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((40/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 43 : ℕ) : ℝ) / ((42 : ℕ) : ℝ)) = ((41/42 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41]
  try ring

def cotangentSumVFormula_43_42_lower : ℚ := -919069349054090016319 / 27487790694400000000
def cotangentSumVFormula_43_42_upper : ℚ := -919069348504313889931 / 27487790694400000000
theorem cotangentSumVFormula_43_42_bounds :
  ((cotangentSumVFormula_43_42_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 43 42 ∧
  cotangentSumVFormula 43 42 ≤ ((cotangentSumVFormula_43_42_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_43_42_unfold]
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
  rw [cotangentSumVFormula_43_42_lower, cotangentSumVFormula_43_42_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_4243_formula_bound :
  (((129223396042019738879 / 4503599627370496000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 42 43) ∧
  (vasyuninBEntryFormula 42 43 ≤ ((129232403241280198621 / 4503599627370496000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 42 43 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log42 := prim_log_42_bounds
  have b_log43 := log_43_certified_bounds
  have b_Vhk := cotangentSumVFormula_42_43_bounds
  have b_Vkh := cotangentSumVFormula_43_42_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_42_lower, prim_log_42_upper] at b_log42
  simp only [log_43_lower, log_43_upper] at b_log43
  simp only [cotangentSumVFormula_42_43_lower, cotangentSumVFormula_42_43_upper] at b_Vhk
  simp only [cotangentSumVFormula_43_42_lower, cotangentSumVFormula_43_42_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_44_unfold :
    cotangentSumVFormula 1 44 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 1 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_1_44_lower : ℚ := -980322051446101735069 / 27487790694400000000
def cotangentSumVFormula_1_44_upper : ℚ := -490161025448160655903 / 13743895347200000000
theorem cotangentSumVFormula_1_44_bounds :
  ((cotangentSumVFormula_1_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 44 ∧
  cotangentSumVFormula 1 44 ≤ ((cotangentSumVFormula_1_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_44_unfold]
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
  rw [cotangentSumVFormula_1_44_lower, cotangentSumVFormula_1_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_1_unfold :
    cotangentSumVFormula 44 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_44_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_44_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_44_1_bounds :
  ((cotangentSumVFormula_44_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 1 ∧
  cotangentSumVFormula 44 1 ≤ ((cotangentSumVFormula_44_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_1_unfold]
  rw [cotangentSumVFormula_44_1_lower, cotangentSumVFormula_44_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_144_formula_bound :
  (((77418331471227235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 44) ∧
  (vasyuninBEntryFormula 1 44 ≤ ((77420583271081264499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_1_44_bounds
  have b_Vkh := cotangentSumVFormula_44_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_1_44_lower, cotangentSumVFormula_1_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_1_lower, cotangentSumVFormula_44_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_44_unfold :
    cotangentSumVFormula 3 44 =
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
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 3 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_3_44_lower : ℚ := -290007635017090125347 / 13743895347200000000
def cotangentSumVFormula_3_44_upper : ℚ := -1160030538968800826737 / 54975581388800000000
theorem cotangentSumVFormula_3_44_bounds :
  ((cotangentSumVFormula_3_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 44 ∧
  cotangentSumVFormula 3 44 ≤ ((cotangentSumVFormula_3_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_44_unfold]
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
  rw [cotangentSumVFormula_3_44_lower, cotangentSumVFormula_3_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_3_unfold :
    cotangentSumVFormula 44 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_44_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_44_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_44_3_bounds :
  ((cotangentSumVFormula_44_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 3 ∧
  cotangentSumVFormula 44 3 ≤ ((cotangentSumVFormula_44_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_44_3_lower, cotangentSumVFormula_44_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_344_formula_bound :
  (((63237070618445829251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 44) ∧
  (vasyuninBEntryFormula 3 44 ≤ ((63239322418272545749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_3_44_bounds
  have b_Vkh := cotangentSumVFormula_44_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_3_44_lower, cotangentSumVFormula_3_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_3_lower, cotangentSumVFormula_44_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_44_unfold :
    cotangentSumVFormula 5 44 =
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
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 5 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_5_44_lower : ℚ := -3360474024607540052427 / 219902325555200000000
def cotangentSumVFormula_5_44_upper : ℚ := -3360474020209309166323 / 219902325555200000000
theorem cotangentSumVFormula_5_44_bounds :
  ((cotangentSumVFormula_5_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 44 ∧
  cotangentSumVFormula 5 44 ≤ ((cotangentSumVFormula_5_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_44_unfold]
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
  rw [cotangentSumVFormula_5_44_lower, cotangentSumVFormula_5_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_5_unfold :
    cotangentSumVFormula 44 5 =
      ((4/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_44_5_lower : ℚ := 3134269892212533770543 / 3518437208883200000000
def cotangentSumVFormula_44_5_upper : ℚ := 3134269962581292010707 / 3518437208883200000000
theorem cotangentSumVFormula_44_5_bounds :
  ((cotangentSumVFormula_44_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 5 ∧
  cotangentSumVFormula 44 5 ≤ ((cotangentSumVFormula_44_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_44_5_lower, cotangentSumVFormula_44_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_544_formula_bound :
  (((113443889441109049127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 44) ∧
  (vasyuninBEntryFormula 5 44 ≤ ((113448393040751263373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_5_44_bounds
  have b_Vkh := cotangentSumVFormula_44_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_5_44_lower, cotangentSumVFormula_5_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_5_lower, cotangentSumVFormula_44_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_44_unfold :
    cotangentSumVFormula 7 44 =
      ((7/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 7 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_7_44_lower : ℚ := -2130551878356062708677 / 219902325555200000000
def cotangentSumVFormula_7_44_upper : ℚ := -2130551873957825572573 / 219902325555200000000
theorem cotangentSumVFormula_7_44_bounds :
  ((cotangentSumVFormula_7_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 44 ∧
  cotangentSumVFormula 7 44 ≤ ((cotangentSumVFormula_7_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_44_unfold]
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
  rw [cotangentSumVFormula_7_44_lower, cotangentSumVFormula_7_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_7_unfold :
    cotangentSumVFormula 44 7 =
      ((2/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_44_7_lower : ℚ := -269592303162212526729 / 439804651110400000000
def cotangentSumVFormula_44_7_upper : ℚ := -539184588732231587167 / 879609302220800000000
theorem cotangentSumVFormula_44_7_bounds :
  ((cotangentSumVFormula_44_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 7 ∧
  cotangentSumVFormula 44 7 ≤ ((cotangentSumVFormula_44_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_7_unfold]
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
  rw [cotangentSumVFormula_44_7_lower, cotangentSumVFormula_44_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_744_formula_bound :
  (((13086867069029492469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 44) ∧
  (vasyuninBEntryFormula 7 44 ≤ ((52349720075937076999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_7_44_bounds
  have b_Vkh := cotangentSumVFormula_44_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_7_44_lower, cotangentSumVFormula_7_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_7_lower, cotangentSumVFormula_44_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_44_unfold :
    cotangentSumVFormula 9 44 =
      ((9/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 9 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_9_44_lower : ℚ := -575770728095578079513 / 54975581388800000000
def cotangentSumVFormula_9_44_upper : ℚ := -575770726996021920487 / 54975581388800000000
theorem cotangentSumVFormula_9_44_bounds :
  ((cotangentSumVFormula_9_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 44 ∧
  cotangentSumVFormula 9 44 ≤ ((cotangentSumVFormula_9_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_44_unfold]
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
  rw [cotangentSumVFormula_9_44_lower, cotangentSumVFormula_9_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_9_unfold :
    cotangentSumVFormula 44 9 =
      ((8/9 : ℚ) : ℝ) * cotangentTermV 1 9    + 
      ((7/9 : ℚ) : ℝ) * cotangentTermV 2 9    + 
      ((6/9 : ℚ) : ℝ) * cotangentTermV 3 9    + 
      ((5/9 : ℚ) : ℝ) * cotangentTermV 4 9    + 
      ((4/9 : ℚ) : ℝ) * cotangentTermV 5 9    + 
      ((3/9 : ℚ) : ℝ) * cotangentTermV 6 9    + 
      ((2/9 : ℚ) : ℝ) * cotangentTermV 7 9    + 
      ((1/9 : ℚ) : ℝ) * cotangentTermV 8 9 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_9]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_44_9_lower : ℚ := 1324275632006511692021 / 439804651110400000000
def cotangentSumVFormula_44_9_upper : ℚ := 165534455100326517013 / 54975581388800000000
theorem cotangentSumVFormula_44_9_bounds :
  ((cotangentSumVFormula_44_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 9 ∧
  cotangentSumVFormula 44 9 ≤ ((cotangentSumVFormula_44_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_9_unfold]
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
  rw [cotangentSumVFormula_44_9_lower, cotangentSumVFormula_44_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_944_formula_bound :
  (((98696882080533705377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 44) ∧
  (vasyuninBEntryFormula 9 44 ≤ ((98701385680169138373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_9_44_bounds
  have b_Vkh := cotangentSumVFormula_44_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_9_44_lower, cotangentSumVFormula_9_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_9_lower, cotangentSumVFormula_44_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_44_unfold :
    cotangentSumVFormula 13 44 =
      ((13/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 13 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_13_44_lower : ℚ := -2737988178927875444083 / 879609302220800000000
def cotangentSumVFormula_13_44_upper : ℚ := -2737988161335004243417 / 879609302220800000000
theorem cotangentSumVFormula_13_44_bounds :
  ((cotangentSumVFormula_13_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 44 ∧
  cotangentSumVFormula 13 44 ≤ ((cotangentSumVFormula_13_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_44_unfold]
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
  rw [cotangentSumVFormula_13_44_lower, cotangentSumVFormula_13_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_13_unfold :
    cotangentSumVFormula 44 13 =
      ((5/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_44_13_lower : ℚ := -2564725761354090662039 / 7036874417766400000000
def cotangentSumVFormula_44_13_upper : ℚ := -2564725620616296837961 / 7036874417766400000000
theorem cotangentSumVFormula_44_13_bounds :
  ((cotangentSumVFormula_44_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 13 ∧
  cotangentSumVFormula 44 13 ≤ ((cotangentSumVFormula_44_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_13_unfold]
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
  rw [cotangentSumVFormula_44_13_lower, cotangentSumVFormula_44_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1344_formula_bound :
  (((88544662767358424127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 44) ∧
  (vasyuninBEntryFormula 13 44 ≤ ((88549166366991294623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_13_44_bounds
  have b_Vkh := cotangentSumVFormula_44_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_13_44_lower, cotangentSumVFormula_13_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_13_lower, cotangentSumVFormula_44_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_44_unfold :
    cotangentSumVFormula 15 44 =
      ((15/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 15 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_15_44_lower : ℚ := -1054094869762412018401 / 109951162777600000000
def cotangentSumVFormula_15_44_upper : ℚ := -1054094867563303606599 / 109951162777600000000
theorem cotangentSumVFormula_15_44_bounds :
  ((cotangentSumVFormula_15_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 44 ∧
  cotangentSumVFormula 15 44 ≤ ((cotangentSumVFormula_15_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_44_unfold]
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
  rw [cotangentSumVFormula_15_44_lower, cotangentSumVFormula_15_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_15_unfold :
    cotangentSumVFormula 44 15 =
      ((14/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((4/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_44_15_lower : ℚ := 1590970984054520885073 / 219902325555200000000
def cotangentSumVFormula_44_15_upper : ℚ := 397742747113145267013 / 54975581388800000000
theorem cotangentSumVFormula_44_15_bounds :
  ((cotangentSumVFormula_44_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 15 ∧
  cotangentSumVFormula 44 15 ≤ ((cotangentSumVFormula_44_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_15_unfold]
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
  rw [cotangentSumVFormula_44_15_lower, cotangentSumVFormula_44_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1544_formula_bound :
  (((86248720030126142877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 44) ∧
  (vasyuninBEntryFormula 15 44 ≤ ((86253223629758325873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_15_44_bounds
  have b_Vkh := cotangentSumVFormula_44_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_15_44_lower, cotangentSumVFormula_15_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_15_lower, cotangentSumVFormula_44_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_44_unfold :
    cotangentSumVFormula 17 44 =
      ((17/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 17 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_17_44_lower : ℚ := -2179829228150114560041 / 1759218604441600000000
def cotangentSumVFormula_17_44_upper : ℚ := -2179829192964413564959 / 1759218604441600000000
theorem cotangentSumVFormula_17_44_bounds :
  ((cotangentSumVFormula_17_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 44 ∧
  cotangentSumVFormula 17 44 ≤ ((cotangentSumVFormula_17_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_44_unfold]
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
  rw [cotangentSumVFormula_17_44_lower, cotangentSumVFormula_17_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_17_unfold :
    cotangentSumVFormula 44 17 =
      ((10/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_44_17_lower : ℚ := 2268486003667060119211 / 7036874417766400000000
def cotangentSumVFormula_44_17_upper : ℚ := 2268486144405121130789 / 7036874417766400000000
theorem cotangentSumVFormula_44_17_bounds :
  ((cotangentSumVFormula_44_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 17 ∧
  cotangentSumVFormula 44 17 ≤ ((cotangentSumVFormula_44_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_17_unfold]
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
  rw [cotangentSumVFormula_44_17_lower, cotangentSumVFormula_44_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1744_formula_bound :
  (((81435745389042486627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 44) ∧
  (vasyuninBEntryFormula 17 44 ≤ ((81440248988674075873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_17_44_bounds
  have b_Vkh := cotangentSumVFormula_44_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_17_44_lower, cotangentSumVFormula_17_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_17_lower, cotangentSumVFormula_44_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_44_unfold :
    cotangentSumVFormula 19 44 =
      ((19/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 19 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_19_44_lower : ℚ := -1604873195071594995953 / 14073748835532800000000
def cotangentSumVFormula_19_44_upper : ℚ := -1604872913586305004047 / 14073748835532800000000
theorem cotangentSumVFormula_19_44_bounds :
  ((cotangentSumVFormula_19_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 44 ∧
  cotangentSumVFormula 19 44 ≤ ((cotangentSumVFormula_19_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_44_unfold]
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
  rw [cotangentSumVFormula_19_44_lower, cotangentSumVFormula_19_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_19_unfold :
    cotangentSumVFormula 44 19 =
      ((6/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_44_19_lower : ℚ := 2270957573391257273719 / 28147497671065600000000
def cotangentSumVFormula_44_19_upper : ℚ := 2270958136343992726281 / 28147497671065600000000
theorem cotangentSumVFormula_44_19_bounds :
  ((cotangentSumVFormula_44_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 19 ∧
  cotangentSumVFormula 44 19 ≤ ((cotangentSumVFormula_44_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_19_unfold]
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
  rw [cotangentSumVFormula_44_19_lower, cotangentSumVFormula_44_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1944_formula_bound :
  (((39413910551629360501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 44) ∧
  (vasyuninBEntryFormula 19 44 ≤ ((39416162351444951999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_19_44_bounds
  have b_Vkh := cotangentSumVFormula_44_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_19_44_lower, cotangentSumVFormula_19_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_19_lower, cotangentSumVFormula_44_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_21_44_unfold :
    cotangentSumVFormula 21 44 =
      ((21/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((23/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 21 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_21_44_lower : ℚ := 1820829586145502135073 / 219902325555200000000
def cotangentSumVFormula_21_44_upper : ℚ := 1820829590543703333677 / 219902325555200000000
theorem cotangentSumVFormula_21_44_bounds :
  ((cotangentSumVFormula_21_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 21 44 ∧
  cotangentSumVFormula 21 44 ≤ ((cotangentSumVFormula_21_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_21_44_unfold]
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
  rw [cotangentSumVFormula_21_44_lower, cotangentSumVFormula_21_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_21_unfold :
    cotangentSumVFormula 44 21 =
      ((2/21 : ℚ) : ℝ) * cotangentTermV 1 21    + 
      ((4/21 : ℚ) : ℝ) * cotangentTermV 2 21    + 
      ((6/21 : ℚ) : ℝ) * cotangentTermV 3 21    + 
      ((8/21 : ℚ) : ℝ) * cotangentTermV 4 21    + 
      ((10/21 : ℚ) : ℝ) * cotangentTermV 5 21    + 
      ((12/21 : ℚ) : ℝ) * cotangentTermV 6 21    + 
      ((14/21 : ℚ) : ℝ) * cotangentTermV 7 21    + 
      ((16/21 : ℚ) : ℝ) * cotangentTermV 8 21    + 
      ((18/21 : ℚ) : ℝ) * cotangentTermV 9 21    + 
      ((20/21 : ℚ) : ℝ) * cotangentTermV 10 21    + 
      ((1/21 : ℚ) : ℝ) * cotangentTermV 11 21    + 
      ((3/21 : ℚ) : ℝ) * cotangentTermV 12 21    + 
      ((5/21 : ℚ) : ℝ) * cotangentTermV 13 21    + 
      ((7/21 : ℚ) : ℝ) * cotangentTermV 14 21    + 
      ((9/21 : ℚ) : ℝ) * cotangentTermV 15 21    + 
      ((11/21 : ℚ) : ℝ) * cotangentTermV 16 21    + 
      ((13/21 : ℚ) : ℝ) * cotangentTermV 17 21    + 
      ((15/21 : ℚ) : ℝ) * cotangentTermV 18 21    + 
      ((17/21 : ℚ) : ℝ) * cotangentTermV 19 21    + 
      ((19/21 : ℚ) : ℝ) * cotangentTermV 20 21 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_21]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((2/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((4/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((6/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((8/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((10/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((12/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((14/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((16/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((18/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((20/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((1/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((3/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((5/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((7/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((9/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((11/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((13/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((15/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((17/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((19/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20]
  try ring

def cotangentSumVFormula_44_21_lower : ℚ := -435705372582548392013 / 54975581388800000000
def cotangentSumVFormula_44_21_upper : ℚ := -435705371483029732987 / 54975581388800000000
theorem cotangentSumVFormula_44_21_bounds :
  ((cotangentSumVFormula_44_21_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 21 ∧
  cotangentSumVFormula 44 21 ≤ ((cotangentSumVFormula_44_21_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_21_unfold]
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
  rw [cotangentSumVFormula_44_21_lower, cotangentSumVFormula_44_21_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2144_formula_bound :
  (((77758193094420830377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 21 44) ∧
  (vasyuninBEntryFormula 21 44 ≤ ((77762696694051669623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 21 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log21 := prim_log_21_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_21_44_bounds
  have b_Vkh := cotangentSumVFormula_44_21_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_21_lower, prim_log_21_upper] at b_log21
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_21_44_lower, cotangentSumVFormula_21_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_21_lower, cotangentSumVFormula_44_21_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_44_unfold :
    cotangentSumVFormula 23 44 =
      ((23/44 : ℚ) : ℝ) * cotangentTermV 1 44    + 
      ((2/44 : ℚ) : ℝ) * cotangentTermV 2 44    + 
      ((25/44 : ℚ) : ℝ) * cotangentTermV 3 44    + 
      ((4/44 : ℚ) : ℝ) * cotangentTermV 4 44    + 
      ((27/44 : ℚ) : ℝ) * cotangentTermV 5 44    + 
      ((6/44 : ℚ) : ℝ) * cotangentTermV 6 44    + 
      ((29/44 : ℚ) : ℝ) * cotangentTermV 7 44    + 
      ((8/44 : ℚ) : ℝ) * cotangentTermV 8 44    + 
      ((31/44 : ℚ) : ℝ) * cotangentTermV 9 44    + 
      ((10/44 : ℚ) : ℝ) * cotangentTermV 10 44    + 
      ((33/44 : ℚ) : ℝ) * cotangentTermV 11 44    + 
      ((12/44 : ℚ) : ℝ) * cotangentTermV 12 44    + 
      ((35/44 : ℚ) : ℝ) * cotangentTermV 13 44    + 
      ((14/44 : ℚ) : ℝ) * cotangentTermV 14 44    + 
      ((37/44 : ℚ) : ℝ) * cotangentTermV 15 44    + 
      ((16/44 : ℚ) : ℝ) * cotangentTermV 16 44    + 
      ((39/44 : ℚ) : ℝ) * cotangentTermV 17 44    + 
      ((18/44 : ℚ) : ℝ) * cotangentTermV 18 44    + 
      ((41/44 : ℚ) : ℝ) * cotangentTermV 19 44    + 
      ((20/44 : ℚ) : ℝ) * cotangentTermV 20 44    + 
      ((43/44 : ℚ) : ℝ) * cotangentTermV 21 44    + 
      ((22/44 : ℚ) : ℝ) * cotangentTermV 22 44    + 
      ((1/44 : ℚ) : ℝ) * cotangentTermV 23 44    + 
      ((24/44 : ℚ) : ℝ) * cotangentTermV 24 44    + 
      ((3/44 : ℚ) : ℝ) * cotangentTermV 25 44    + 
      ((26/44 : ℚ) : ℝ) * cotangentTermV 26 44    + 
      ((5/44 : ℚ) : ℝ) * cotangentTermV 27 44    + 
      ((28/44 : ℚ) : ℝ) * cotangentTermV 28 44    + 
      ((7/44 : ℚ) : ℝ) * cotangentTermV 29 44    + 
      ((30/44 : ℚ) : ℝ) * cotangentTermV 30 44    + 
      ((9/44 : ℚ) : ℝ) * cotangentTermV 31 44    + 
      ((32/44 : ℚ) : ℝ) * cotangentTermV 32 44    + 
      ((11/44 : ℚ) : ℝ) * cotangentTermV 33 44    + 
      ((34/44 : ℚ) : ℝ) * cotangentTermV 34 44    + 
      ((13/44 : ℚ) : ℝ) * cotangentTermV 35 44    + 
      ((36/44 : ℚ) : ℝ) * cotangentTermV 36 44    + 
      ((15/44 : ℚ) : ℝ) * cotangentTermV 37 44    + 
      ((38/44 : ℚ) : ℝ) * cotangentTermV 38 44    + 
      ((17/44 : ℚ) : ℝ) * cotangentTermV 39 44    + 
      ((40/44 : ℚ) : ℝ) * cotangentTermV 40 44    + 
      ((19/44 : ℚ) : ℝ) * cotangentTermV 41 44    + 
      ((42/44 : ℚ) : ℝ) * cotangentTermV 42 44    + 
      ((21/44 : ℚ) : ℝ) * cotangentTermV 43 44 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_44]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((23/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((2/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((25/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((4/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((27/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((6/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((29/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((8/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((31/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((10/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((33/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((12/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((35/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((14/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((37/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((16/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((39/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((18/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((41/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((20/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((43/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((22/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((1/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((24/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((3/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((26/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((5/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((28/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((7/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((30/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((9/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((32/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((11/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((34/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((13/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((36/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_37 : Int.fract (((37 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((15/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_38 : Int.fract (((38 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((38/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_39 : Int.fract (((39 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((17/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_40 : Int.fract (((40 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((40/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_41 : Int.fract (((41 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((19/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_42 : Int.fract (((42 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((42/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_43 : Int.fract (((43 * 23 : ℕ) : ℝ) / ((44 : ℕ) : ℝ)) = ((21/44 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36, hf_37, hf_38, hf_39, hf_40, hf_41, hf_42, hf_43]
  try ring

def cotangentSumVFormula_23_44_lower : ℚ := -1820829590543691614927 / 219902325555200000000
def cotangentSumVFormula_23_44_upper : ℚ := -1820829586145484166323 / 219902325555200000000
theorem cotangentSumVFormula_23_44_bounds :
  ((cotangentSumVFormula_23_44_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 44 ∧
  cotangentSumVFormula 23 44 ≤ ((cotangentSumVFormula_23_44_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_44_unfold]
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
  rw [cotangentSumVFormula_23_44_lower, cotangentSumVFormula_23_44_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_44_23_unfold :
    cotangentSumVFormula 44 23 =
      ((21/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 44 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_44_23_lower : ℚ := 2042012866442354478823 / 219902325555200000000
def cotangentSumVFormula_44_23_upper : ℚ := 2042012870840431458677 / 219902325555200000000
theorem cotangentSumVFormula_44_23_bounds :
  ((cotangentSumVFormula_44_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 44 23 ∧
  cotangentSumVFormula 44 23 ≤ ((cotangentSumVFormula_44_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_44_23_unfold]
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
  rw [cotangentSumVFormula_44_23_lower, cotangentSumVFormula_44_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2344_formula_bound :
  (((75297107739451174127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 44) ∧
  (vasyuninBEntryFormula 23 44 ≤ ((75301611339081857123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 44 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log44 := prim_log_44_bounds
  have b_Vhk := cotangentSumVFormula_23_44_bounds
  have b_Vkh := cotangentSumVFormula_44_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_44_lower, prim_log_44_upper] at b_log44
  simp only [cotangentSumVFormula_23_44_lower, cotangentSumVFormula_23_44_upper] at b_Vhk
  simp only [cotangentSumVFormula_44_23_lower, cotangentSumVFormula_44_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
