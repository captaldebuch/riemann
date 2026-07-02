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

theorem cotangentSumVFormula_22_35_unfold :
    cotangentSumVFormula 22 35 =
      ((22/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 22 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_22_35_lower : ℚ := 2555730202408973721209 / 1759218604441600000000
def cotangentSumVFormula_22_35_upper : ℚ := 2555730237594048153791 / 1759218604441600000000
theorem cotangentSumVFormula_22_35_bounds :
  ((cotangentSumVFormula_22_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 22 35 ∧
  cotangentSumVFormula 22 35 ≤ ((cotangentSumVFormula_22_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_22_35_unfold]
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
  rw [cotangentSumVFormula_22_35_lower, cotangentSumVFormula_22_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_22_unfold :
    cotangentSumVFormula 35 22 =
      ((13/22 : ℚ) : ℝ) * cotangentTermV 1 22    + 
      ((4/22 : ℚ) : ℝ) * cotangentTermV 2 22    + 
      ((17/22 : ℚ) : ℝ) * cotangentTermV 3 22    + 
      ((8/22 : ℚ) : ℝ) * cotangentTermV 4 22    + 
      ((21/22 : ℚ) : ℝ) * cotangentTermV 5 22    + 
      ((12/22 : ℚ) : ℝ) * cotangentTermV 6 22    + 
      ((3/22 : ℚ) : ℝ) * cotangentTermV 7 22    + 
      ((16/22 : ℚ) : ℝ) * cotangentTermV 8 22    + 
      ((7/22 : ℚ) : ℝ) * cotangentTermV 9 22    + 
      ((20/22 : ℚ) : ℝ) * cotangentTermV 10 22    + 
      ((11/22 : ℚ) : ℝ) * cotangentTermV 11 22    + 
      ((2/22 : ℚ) : ℝ) * cotangentTermV 12 22    + 
      ((15/22 : ℚ) : ℝ) * cotangentTermV 13 22    + 
      ((6/22 : ℚ) : ℝ) * cotangentTermV 14 22    + 
      ((19/22 : ℚ) : ℝ) * cotangentTermV 15 22    + 
      ((10/22 : ℚ) : ℝ) * cotangentTermV 16 22    + 
      ((1/22 : ℚ) : ℝ) * cotangentTermV 17 22    + 
      ((14/22 : ℚ) : ℝ) * cotangentTermV 18 22    + 
      ((5/22 : ℚ) : ℝ) * cotangentTermV 19 22    + 
      ((18/22 : ℚ) : ℝ) * cotangentTermV 20 22    + 
      ((9/22 : ℚ) : ℝ) * cotangentTermV 21 22 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_22]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((13/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((4/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((17/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((8/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((21/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((12/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((3/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((16/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((7/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((20/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((11/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((2/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((15/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((6/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((19/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((10/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((1/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((14/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((5/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((18/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((9/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21]
  try ring

def cotangentSumVFormula_35_22_lower : ℚ := 2625817846831270489293 / 3518437208883200000000
def cotangentSumVFormula_35_22_upper : ℚ := 2625817917200573260707 / 3518437208883200000000
theorem cotangentSumVFormula_35_22_bounds :
  ((cotangentSumVFormula_35_22_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 22 ∧
  cotangentSumVFormula 35 22 ≤ ((cotangentSumVFormula_35_22_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_22_unfold]
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
  rw [cotangentSumVFormula_35_22_lower, cotangentSumVFormula_35_22_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2235_formula_bound :
  (((86141015369014767877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 22 35) ∧
  (vasyuninBEntryFormula 22 35 ≤ ((86145518968644982123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 22 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log22 := prim_log_22_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_22_35_bounds
  have b_Vkh := cotangentSumVFormula_35_22_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_22_lower, prim_log_22_upper] at b_log22
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_22_35_lower, cotangentSumVFormula_22_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_22_lower, cotangentSumVFormula_35_22_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_35_unfold :
    cotangentSumVFormula 23 35 =
      ((23/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_23_35_lower : ℚ := 23366652209024246007 / 3435973836800000000
def cotangentSumVFormula_23_35_upper : ℚ := 747732872887844830901 / 109951162777600000000
theorem cotangentSumVFormula_23_35_bounds :
  ((cotangentSumVFormula_23_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 35 ∧
  cotangentSumVFormula 23 35 ≤ ((cotangentSumVFormula_23_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_35_unfold]
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
  rw [cotangentSumVFormula_23_35_lower, cotangentSumVFormula_23_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_23_unfold :
    cotangentSumVFormula 35 23 =
      ((12/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_35_23_lower : ℚ := -987883732647374427427 / 219902325555200000000
def cotangentSumVFormula_35_23_upper : ℚ := -246970932062321920487 / 54975581388800000000
theorem cotangentSumVFormula_35_23_bounds :
  ((cotangentSumVFormula_35_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 23 ∧
  cotangentSumVFormula 35 23 ≤ ((cotangentSumVFormula_35_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_23_unfold]
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
  rw [cotangentSumVFormula_35_23_lower, cotangentSumVFormula_35_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2335_formula_bound :
  (((21268679834601375563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 35) ∧
  (vasyuninBEntryFormula 23 35 ≤ ((21269805734508936937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_23_35_bounds
  have b_Vkh := cotangentSumVFormula_35_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_23_35_lower, cotangentSumVFormula_23_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_23_lower, cotangentSumVFormula_35_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_24_35_unfold :
    cotangentSumVFormula 24 35 =
      ((24/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 24 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_24_35_lower : ℚ := 2379352407249083910297 / 14073748835532800000000
def cotangentSumVFormula_24_35_upper : ℚ := 2379352688729078589703 / 14073748835532800000000
theorem cotangentSumVFormula_24_35_bounds :
  ((cotangentSumVFormula_24_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 24 35 ∧
  cotangentSumVFormula 24 35 ≤ ((cotangentSumVFormula_24_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_24_35_unfold]
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
  rw [cotangentSumVFormula_24_35_lower, cotangentSumVFormula_24_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_24_unfold :
    cotangentSumVFormula 35 24 =
      ((11/24 : ℚ) : ℝ) * cotangentTermV 1 24    + 
      ((22/24 : ℚ) : ℝ) * cotangentTermV 2 24    + 
      ((9/24 : ℚ) : ℝ) * cotangentTermV 3 24    + 
      ((20/24 : ℚ) : ℝ) * cotangentTermV 4 24    + 
      ((7/24 : ℚ) : ℝ) * cotangentTermV 5 24    + 
      ((18/24 : ℚ) : ℝ) * cotangentTermV 6 24    + 
      ((5/24 : ℚ) : ℝ) * cotangentTermV 7 24    + 
      ((16/24 : ℚ) : ℝ) * cotangentTermV 8 24    + 
      ((3/24 : ℚ) : ℝ) * cotangentTermV 9 24    + 
      ((14/24 : ℚ) : ℝ) * cotangentTermV 10 24    + 
      ((1/24 : ℚ) : ℝ) * cotangentTermV 11 24    + 
      ((12/24 : ℚ) : ℝ) * cotangentTermV 12 24    + 
      ((23/24 : ℚ) : ℝ) * cotangentTermV 13 24    + 
      ((10/24 : ℚ) : ℝ) * cotangentTermV 14 24    + 
      ((21/24 : ℚ) : ℝ) * cotangentTermV 15 24    + 
      ((8/24 : ℚ) : ℝ) * cotangentTermV 16 24    + 
      ((19/24 : ℚ) : ℝ) * cotangentTermV 17 24    + 
      ((6/24 : ℚ) : ℝ) * cotangentTermV 18 24    + 
      ((17/24 : ℚ) : ℝ) * cotangentTermV 19 24    + 
      ((4/24 : ℚ) : ℝ) * cotangentTermV 20 24    + 
      ((15/24 : ℚ) : ℝ) * cotangentTermV 21 24    + 
      ((2/24 : ℚ) : ℝ) * cotangentTermV 22 24    + 
      ((13/24 : ℚ) : ℝ) * cotangentTermV 23 24 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_24]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((11/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((22/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((9/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((20/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((7/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((18/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((5/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((16/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((3/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((14/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((1/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((12/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((23/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((10/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((21/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((8/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((19/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((6/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((17/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((4/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((15/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((2/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((13/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23]
  try ring

def cotangentSumVFormula_35_24_lower : ℚ := 1030620032138747629521 / 439804651110400000000
def cotangentSumVFormula_35_24_upper : ℚ := 1030620040934926589229 / 439804651110400000000
theorem cotangentSumVFormula_35_24_bounds :
  ((cotangentSumVFormula_35_24_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 24 ∧
  cotangentSumVFormula 35 24 ≤ ((cotangentSumVFormula_35_24_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_24_unfold]
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
  rw [cotangentSumVFormula_35_24_lower, cotangentSumVFormula_35_24_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2435_formula_bound :
  (((41774974768194079251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 24 35) ∧
  (vasyuninBEntryFormula 24 35 ≤ ((20888613284004530687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 24 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log24 := prim_log_24_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_24_35_bounds
  have b_Vkh := cotangentSumVFormula_35_24_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_24_lower, prim_log_24_upper] at b_log24
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_24_35_lower, cotangentSumVFormula_24_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_24_lower, cotangentSumVFormula_35_24_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_26_35_unfold :
    cotangentSumVFormula 26 35 =
      ((26/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 26 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_26_35_lower : ℚ := 1538130330478290416323 / 219902325555200000000
def cotangentSumVFormula_26_35_upper : ℚ := 1538130334876418958677 / 219902325555200000000
theorem cotangentSumVFormula_26_35_bounds :
  ((cotangentSumVFormula_26_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 26 35 ∧
  cotangentSumVFormula 26 35 ≤ ((cotangentSumVFormula_26_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_26_35_unfold]
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
  rw [cotangentSumVFormula_26_35_lower, cotangentSumVFormula_26_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_26_unfold :
    cotangentSumVFormula 35 26 =
      ((9/26 : ℚ) : ℝ) * cotangentTermV 1 26    + 
      ((18/26 : ℚ) : ℝ) * cotangentTermV 2 26    + 
      ((1/26 : ℚ) : ℝ) * cotangentTermV 3 26    + 
      ((10/26 : ℚ) : ℝ) * cotangentTermV 4 26    + 
      ((19/26 : ℚ) : ℝ) * cotangentTermV 5 26    + 
      ((2/26 : ℚ) : ℝ) * cotangentTermV 6 26    + 
      ((11/26 : ℚ) : ℝ) * cotangentTermV 7 26    + 
      ((20/26 : ℚ) : ℝ) * cotangentTermV 8 26    + 
      ((3/26 : ℚ) : ℝ) * cotangentTermV 9 26    + 
      ((12/26 : ℚ) : ℝ) * cotangentTermV 10 26    + 
      ((21/26 : ℚ) : ℝ) * cotangentTermV 11 26    + 
      ((4/26 : ℚ) : ℝ) * cotangentTermV 12 26    + 
      ((13/26 : ℚ) : ℝ) * cotangentTermV 13 26    + 
      ((22/26 : ℚ) : ℝ) * cotangentTermV 14 26    + 
      ((5/26 : ℚ) : ℝ) * cotangentTermV 15 26    + 
      ((14/26 : ℚ) : ℝ) * cotangentTermV 16 26    + 
      ((23/26 : ℚ) : ℝ) * cotangentTermV 17 26    + 
      ((6/26 : ℚ) : ℝ) * cotangentTermV 18 26    + 
      ((15/26 : ℚ) : ℝ) * cotangentTermV 19 26    + 
      ((24/26 : ℚ) : ℝ) * cotangentTermV 20 26    + 
      ((7/26 : ℚ) : ℝ) * cotangentTermV 21 26    + 
      ((16/26 : ℚ) : ℝ) * cotangentTermV 22 26    + 
      ((25/26 : ℚ) : ℝ) * cotangentTermV 23 26    + 
      ((8/26 : ℚ) : ℝ) * cotangentTermV 24 26    + 
      ((17/26 : ℚ) : ℝ) * cotangentTermV 25 26 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_26]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((9/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((18/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((1/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((10/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((19/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((2/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((11/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((20/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((3/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((12/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((21/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((4/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((13/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((22/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((5/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((14/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((23/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((6/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((15/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((24/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((7/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((16/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((25/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((8/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((17/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25]
  try ring

def cotangentSumVFormula_35_26_lower : ℚ := -1875166169800838307979 / 439804651110400000000
def cotangentSumVFormula_35_26_upper : ℚ := -1875166161004639035771 / 439804651110400000000
theorem cotangentSumVFormula_35_26_bounds :
  ((cotangentSumVFormula_35_26_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 26 ∧
  cotangentSumVFormula 35 26 ≤ ((cotangentSumVFormula_35_26_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_26_unfold]
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
  rw [cotangentSumVFormula_35_26_lower, cotangentSumVFormula_35_26_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2635_formula_bound :
  (((81217789452514767877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 26 35) ∧
  (vasyuninBEntryFormula 26 35 ≤ ((81222293052144794623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 26 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log26 := prim_log_26_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_26_35_bounds
  have b_Vkh := cotangentSumVFormula_35_26_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_26_lower, prim_log_26_upper] at b_log26
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_26_35_lower, cotangentSumVFormula_26_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_26_lower, cotangentSumVFormula_35_26_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_27_35_unfold :
    cotangentSumVFormula 27 35 =
      ((27/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 27 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_27_35_lower : ℚ := 987865176524335728823 / 219902325555200000000
def cotangentSumVFormula_27_35_upper : ℚ := 987865180922462708677 / 219902325555200000000
theorem cotangentSumVFormula_27_35_bounds :
  ((cotangentSumVFormula_27_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 27 35 ∧
  cotangentSumVFormula 27 35 ≤ ((cotangentSumVFormula_27_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_27_35_unfold]
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
  rw [cotangentSumVFormula_27_35_lower, cotangentSumVFormula_27_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_27_unfold :
    cotangentSumVFormula 35 27 =
      ((8/27 : ℚ) : ℝ) * cotangentTermV 1 27    + 
      ((16/27 : ℚ) : ℝ) * cotangentTermV 2 27    + 
      ((24/27 : ℚ) : ℝ) * cotangentTermV 3 27    + 
      ((5/27 : ℚ) : ℝ) * cotangentTermV 4 27    + 
      ((13/27 : ℚ) : ℝ) * cotangentTermV 5 27    + 
      ((21/27 : ℚ) : ℝ) * cotangentTermV 6 27    + 
      ((2/27 : ℚ) : ℝ) * cotangentTermV 7 27    + 
      ((10/27 : ℚ) : ℝ) * cotangentTermV 8 27    + 
      ((18/27 : ℚ) : ℝ) * cotangentTermV 9 27    + 
      ((26/27 : ℚ) : ℝ) * cotangentTermV 10 27    + 
      ((7/27 : ℚ) : ℝ) * cotangentTermV 11 27    + 
      ((15/27 : ℚ) : ℝ) * cotangentTermV 12 27    + 
      ((23/27 : ℚ) : ℝ) * cotangentTermV 13 27    + 
      ((4/27 : ℚ) : ℝ) * cotangentTermV 14 27    + 
      ((12/27 : ℚ) : ℝ) * cotangentTermV 15 27    + 
      ((20/27 : ℚ) : ℝ) * cotangentTermV 16 27    + 
      ((1/27 : ℚ) : ℝ) * cotangentTermV 17 27    + 
      ((9/27 : ℚ) : ℝ) * cotangentTermV 18 27    + 
      ((17/27 : ℚ) : ℝ) * cotangentTermV 19 27    + 
      ((25/27 : ℚ) : ℝ) * cotangentTermV 20 27    + 
      ((6/27 : ℚ) : ℝ) * cotangentTermV 21 27    + 
      ((14/27 : ℚ) : ℝ) * cotangentTermV 22 27    + 
      ((22/27 : ℚ) : ℝ) * cotangentTermV 23 27    + 
      ((3/27 : ℚ) : ℝ) * cotangentTermV 24 27    + 
      ((11/27 : ℚ) : ℝ) * cotangentTermV 25 27    + 
      ((19/27 : ℚ) : ℝ) * cotangentTermV 26 27 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_27]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((8/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((16/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((24/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((5/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((13/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((21/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((2/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((10/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((18/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((26/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((7/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((15/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((23/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((4/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((12/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((20/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((1/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((9/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((17/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((25/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((6/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((14/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((22/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((3/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((11/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((27 : ℕ) : ℝ)) = ((19/27 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26]
  try ring

def cotangentSumVFormula_35_27_lower : ℚ := -1498533782594980912833 / 879609302220800000000
def cotangentSumVFormula_35_27_upper : ℚ := -1498533765002550337167 / 879609302220800000000
theorem cotangentSumVFormula_35_27_bounds :
  ((cotangentSumVFormula_35_27_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 27 ∧
  cotangentSumVFormula 35 27 ≤ ((cotangentSumVFormula_35_27_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_27_unfold]
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
  rw [cotangentSumVFormula_35_27_lower, cotangentSumVFormula_35_27_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2735_formula_bound :
  (((80209596711689142877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 27 35) ∧
  (vasyuninBEntryFormula 27 35 ≤ ((80214100311319169623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 27 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log27 := prim_log_27_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_27_35_bounds
  have b_Vkh := cotangentSumVFormula_35_27_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_27_lower, prim_log_27_upper] at b_log27
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_27_35_lower, cotangentSumVFormula_27_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_27_lower, cotangentSumVFormula_35_27_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_35_unfold :
    cotangentSumVFormula 29 35 =
      ((29/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_29_35_lower : ℚ := 1948378755084231041323 / 219902325555200000000
def cotangentSumVFormula_29_35_upper : ℚ := 1948378759482356458677 / 219902325555200000000
theorem cotangentSumVFormula_29_35_bounds :
  ((cotangentSumVFormula_29_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 35 ∧
  cotangentSumVFormula 29 35 ≤ ((cotangentSumVFormula_29_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_35_unfold]
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
  rw [cotangentSumVFormula_29_35_lower, cotangentSumVFormula_29_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_29_unfold :
    cotangentSumVFormula 35 29 =
      ((6/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((7/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_35_29_lower : ℚ := -338831973654417142013 / 54975581388800000000
def cotangentSumVFormula_35_29_upper : ℚ := -677663945109783294099 / 109951162777600000000
theorem cotangentSumVFormula_35_29_bounds :
  ((cotangentSumVFormula_35_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 29 ∧
  cotangentSumVFormula 35 29 ≤ ((cotangentSumVFormula_35_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_29_unfold]
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
  rw [cotangentSumVFormula_35_29_lower, cotangentSumVFormula_35_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2935_formula_bound :
  (((19711423118863906813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 35) ∧
  (vasyuninBEntryFormula 29 35 ≤ ((39425098037542701999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_29_35_bounds
  have b_Vkh := cotangentSumVFormula_35_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_29_35_lower, cotangentSumVFormula_29_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_29_lower, cotangentSumVFormula_35_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_35_unfold :
    cotangentSumVFormula 31 35 =
      ((31/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_31_35_lower : ℚ := 1307100909699010637849 / 109951162777600000000
def cotangentSumVFormula_31_35_upper : ℚ := 1307100911898072174651 / 109951162777600000000
theorem cotangentSumVFormula_31_35_bounds :
  ((cotangentSumVFormula_31_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 35 ∧
  cotangentSumVFormula 31 35 ≤ ((cotangentSumVFormula_31_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_35_unfold]
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
  rw [cotangentSumVFormula_31_35_lower, cotangentSumVFormula_31_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_31_unfold :
    cotangentSumVFormula 35 31 =
      ((4/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((5/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_35_31_lower : ℚ := -524087295600570267013 / 54975581388800000000
def cotangentSumVFormula_35_31_upper : ℚ := -524087294501037545487 / 54975581388800000000
theorem cotangentSumVFormula_35_31_bounds :
  ((cotangentSumVFormula_35_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 31 ∧
  cotangentSumVFormula 35 31 ≤ ((cotangentSumVFormula_35_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_31_unfold]
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
  rw [cotangentSumVFormula_35_31_lower, cotangentSumVFormula_35_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3135_formula_bound :
  (((78156999603044236627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 35) ∧
  (vasyuninBEntryFormula 31 35 ≤ ((78161503202674232123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_31_35_bounds
  have b_Vkh := cotangentSumVFormula_35_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_31_35_lower, cotangentSumVFormula_31_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_31_lower, cotangentSumVFormula_35_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_32_35_unfold :
    cotangentSumVFormula 32 35 =
      ((32/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 32 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_32_35_lower : ℚ := 3181625321357606822573 / 219902325555200000000
def cotangentSumVFormula_32_35_upper : ℚ := 3181625325755725989927 / 219902325555200000000
theorem cotangentSumVFormula_32_35_bounds :
  ((cotangentSumVFormula_32_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 32 35 ∧
  cotangentSumVFormula 32 35 ≤ ((cotangentSumVFormula_32_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_32_35_unfold]
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
  rw [cotangentSumVFormula_32_35_lower, cotangentSumVFormula_32_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_32_unfold :
    cotangentSumVFormula 35 32 =
      ((3/32 : ℚ) : ℝ) * cotangentTermV 1 32    + 
      ((6/32 : ℚ) : ℝ) * cotangentTermV 2 32    + 
      ((9/32 : ℚ) : ℝ) * cotangentTermV 3 32    + 
      ((12/32 : ℚ) : ℝ) * cotangentTermV 4 32    + 
      ((15/32 : ℚ) : ℝ) * cotangentTermV 5 32    + 
      ((18/32 : ℚ) : ℝ) * cotangentTermV 6 32    + 
      ((21/32 : ℚ) : ℝ) * cotangentTermV 7 32    + 
      ((24/32 : ℚ) : ℝ) * cotangentTermV 8 32    + 
      ((27/32 : ℚ) : ℝ) * cotangentTermV 9 32    + 
      ((30/32 : ℚ) : ℝ) * cotangentTermV 10 32    + 
      ((1/32 : ℚ) : ℝ) * cotangentTermV 11 32    + 
      ((4/32 : ℚ) : ℝ) * cotangentTermV 12 32    + 
      ((7/32 : ℚ) : ℝ) * cotangentTermV 13 32    + 
      ((10/32 : ℚ) : ℝ) * cotangentTermV 14 32    + 
      ((13/32 : ℚ) : ℝ) * cotangentTermV 15 32    + 
      ((16/32 : ℚ) : ℝ) * cotangentTermV 16 32    + 
      ((19/32 : ℚ) : ℝ) * cotangentTermV 17 32    + 
      ((22/32 : ℚ) : ℝ) * cotangentTermV 18 32    + 
      ((25/32 : ℚ) : ℝ) * cotangentTermV 19 32    + 
      ((28/32 : ℚ) : ℝ) * cotangentTermV 20 32    + 
      ((31/32 : ℚ) : ℝ) * cotangentTermV 21 32    + 
      ((2/32 : ℚ) : ℝ) * cotangentTermV 22 32    + 
      ((5/32 : ℚ) : ℝ) * cotangentTermV 23 32    + 
      ((8/32 : ℚ) : ℝ) * cotangentTermV 24 32    + 
      ((11/32 : ℚ) : ℝ) * cotangentTermV 25 32    + 
      ((14/32 : ℚ) : ℝ) * cotangentTermV 26 32    + 
      ((17/32 : ℚ) : ℝ) * cotangentTermV 27 32    + 
      ((20/32 : ℚ) : ℝ) * cotangentTermV 28 32    + 
      ((23/32 : ℚ) : ℝ) * cotangentTermV 29 32    + 
      ((26/32 : ℚ) : ℝ) * cotangentTermV 30 32    + 
      ((29/32 : ℚ) : ℝ) * cotangentTermV 31 32 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_32]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((3/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((6/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((9/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((12/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((15/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((18/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((21/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((24/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((27/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((30/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((1/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((4/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((7/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((10/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((13/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((16/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((19/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((22/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((25/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((28/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((31/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((2/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((5/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((8/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((11/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((14/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((17/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((20/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((23/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((26/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) = ((29/32 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31]
  try ring

def cotangentSumVFormula_35_32_lower : ℚ := -1364822696521530768401 / 109951162777600000000
def cotangentSumVFormula_35_32_upper : ℚ := -1364822694322477044099 / 109951162777600000000
theorem cotangentSumVFormula_35_32_bounds :
  ((cotangentSumVFormula_35_32_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 32 ∧
  cotangentSumVFormula 35 32 ≤ ((cotangentSumVFormula_35_32_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_32_unfold]
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
  rw [cotangentSumVFormula_35_32_lower, cotangentSumVFormula_35_32_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3235_formula_bound :
  (((78145608546689049127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 32 35) ∧
  (vasyuninBEntryFormula 32 35 ≤ ((78150112146318544623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 32 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log32 := prim_log_32_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_32_35_bounds
  have b_Vkh := cotangentSumVFormula_35_32_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_32_lower, prim_log_32_upper] at b_log32
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_32_35_lower, cotangentSumVFormula_32_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_32_lower, cotangentSumVFormula_35_32_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_33_35_unfold :
    cotangentSumVFormula 33 35 =
      ((33/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 33 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_33_35_lower : ℚ := 2031664331078205950349 / 109951162777600000000
def cotangentSumVFormula_33_35_upper : ℚ := 2031664333277265143401 / 109951162777600000000
theorem cotangentSumVFormula_33_35_bounds :
  ((cotangentSumVFormula_33_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 33 35 ∧
  cotangentSumVFormula 33 35 ≤ ((cotangentSumVFormula_33_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_33_35_unfold]
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
  rw [cotangentSumVFormula_33_35_lower, cotangentSumVFormula_33_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_33_unfold :
    cotangentSumVFormula 35 33 =
      ((2/33 : ℚ) : ℝ) * cotangentTermV 1 33    + 
      ((4/33 : ℚ) : ℝ) * cotangentTermV 2 33    + 
      ((6/33 : ℚ) : ℝ) * cotangentTermV 3 33    + 
      ((8/33 : ℚ) : ℝ) * cotangentTermV 4 33    + 
      ((10/33 : ℚ) : ℝ) * cotangentTermV 5 33    + 
      ((12/33 : ℚ) : ℝ) * cotangentTermV 6 33    + 
      ((14/33 : ℚ) : ℝ) * cotangentTermV 7 33    + 
      ((16/33 : ℚ) : ℝ) * cotangentTermV 8 33    + 
      ((18/33 : ℚ) : ℝ) * cotangentTermV 9 33    + 
      ((20/33 : ℚ) : ℝ) * cotangentTermV 10 33    + 
      ((22/33 : ℚ) : ℝ) * cotangentTermV 11 33    + 
      ((24/33 : ℚ) : ℝ) * cotangentTermV 12 33    + 
      ((26/33 : ℚ) : ℝ) * cotangentTermV 13 33    + 
      ((28/33 : ℚ) : ℝ) * cotangentTermV 14 33    + 
      ((30/33 : ℚ) : ℝ) * cotangentTermV 15 33    + 
      ((32/33 : ℚ) : ℝ) * cotangentTermV 16 33    + 
      ((1/33 : ℚ) : ℝ) * cotangentTermV 17 33    + 
      ((3/33 : ℚ) : ℝ) * cotangentTermV 18 33    + 
      ((5/33 : ℚ) : ℝ) * cotangentTermV 19 33    + 
      ((7/33 : ℚ) : ℝ) * cotangentTermV 20 33    + 
      ((9/33 : ℚ) : ℝ) * cotangentTermV 21 33    + 
      ((11/33 : ℚ) : ℝ) * cotangentTermV 22 33    + 
      ((13/33 : ℚ) : ℝ) * cotangentTermV 23 33    + 
      ((15/33 : ℚ) : ℝ) * cotangentTermV 24 33    + 
      ((17/33 : ℚ) : ℝ) * cotangentTermV 25 33    + 
      ((19/33 : ℚ) : ℝ) * cotangentTermV 26 33    + 
      ((21/33 : ℚ) : ℝ) * cotangentTermV 27 33    + 
      ((23/33 : ℚ) : ℝ) * cotangentTermV 28 33    + 
      ((25/33 : ℚ) : ℝ) * cotangentTermV 29 33    + 
      ((27/33 : ℚ) : ℝ) * cotangentTermV 30 33    + 
      ((29/33 : ℚ) : ℝ) * cotangentTermV 31 33    + 
      ((31/33 : ℚ) : ℝ) * cotangentTermV 32 33 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_33]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((2/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((4/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((6/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((8/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((10/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((12/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((14/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((16/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((18/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((20/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((22/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((24/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((26/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((28/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((30/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((32/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((1/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((3/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((5/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((7/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((9/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((11/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((13/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((15/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((17/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((19/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((21/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((23/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((25/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((27/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((29/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((33 : ℕ) : ℝ)) = ((31/33 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32]
  try ring

def cotangentSumVFormula_35_33_lower : ℚ := -1851595019725885455901 / 109951162777600000000
def cotangentSumVFormula_35_33_upper : ℚ := -1851595017526824700349 / 109951162777600000000
theorem cotangentSumVFormula_35_33_bounds :
  ((cotangentSumVFormula_35_33_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 33 ∧
  cotangentSumVFormula 35 33 ≤ ((cotangentSumVFormula_35_33_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_33_unfold]
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
  rw [cotangentSumVFormula_35_33_lower, cotangentSumVFormula_35_33_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3335_formula_bound :
  (((39216376823251048001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 33 35) ∧
  (vasyuninBEntryFormula 33 35 ≤ ((39218628623065858249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 33 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log33 := prim_log_33_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_33_35_bounds
  have b_Vkh := cotangentSumVFormula_35_33_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_33_lower, prim_log_33_upper] at b_log33
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_33_35_lower, cotangentSumVFormula_33_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_33_lower, cotangentSumVFormula_35_33_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_34_35_unfold :
    cotangentSumVFormula 34 35 =
      ((34/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((1/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 34 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_34_35_lower : ℚ := 2846146739961264544099 / 109951162777600000000
def cotangentSumVFormula_34_35_upper : ℚ := 2846146742160319830901 / 109951162777600000000
theorem cotangentSumVFormula_34_35_bounds :
  ((cotangentSumVFormula_34_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 34 35 ∧
  cotangentSumVFormula 34 35 ≤ ((cotangentSumVFormula_34_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_34_35_unfold]
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
  rw [cotangentSumVFormula_34_35_lower, cotangentSumVFormula_34_35_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_35_34_unfold :
    cotangentSumVFormula 35 34 =
      ((1/34 : ℚ) : ℝ) * cotangentTermV 1 34    + 
      ((2/34 : ℚ) : ℝ) * cotangentTermV 2 34    + 
      ((3/34 : ℚ) : ℝ) * cotangentTermV 3 34    + 
      ((4/34 : ℚ) : ℝ) * cotangentTermV 4 34    + 
      ((5/34 : ℚ) : ℝ) * cotangentTermV 5 34    + 
      ((6/34 : ℚ) : ℝ) * cotangentTermV 6 34    + 
      ((7/34 : ℚ) : ℝ) * cotangentTermV 7 34    + 
      ((8/34 : ℚ) : ℝ) * cotangentTermV 8 34    + 
      ((9/34 : ℚ) : ℝ) * cotangentTermV 9 34    + 
      ((10/34 : ℚ) : ℝ) * cotangentTermV 10 34    + 
      ((11/34 : ℚ) : ℝ) * cotangentTermV 11 34    + 
      ((12/34 : ℚ) : ℝ) * cotangentTermV 12 34    + 
      ((13/34 : ℚ) : ℝ) * cotangentTermV 13 34    + 
      ((14/34 : ℚ) : ℝ) * cotangentTermV 14 34    + 
      ((15/34 : ℚ) : ℝ) * cotangentTermV 15 34    + 
      ((16/34 : ℚ) : ℝ) * cotangentTermV 16 34    + 
      ((17/34 : ℚ) : ℝ) * cotangentTermV 17 34    + 
      ((18/34 : ℚ) : ℝ) * cotangentTermV 18 34    + 
      ((19/34 : ℚ) : ℝ) * cotangentTermV 19 34    + 
      ((20/34 : ℚ) : ℝ) * cotangentTermV 20 34    + 
      ((21/34 : ℚ) : ℝ) * cotangentTermV 21 34    + 
      ((22/34 : ℚ) : ℝ) * cotangentTermV 22 34    + 
      ((23/34 : ℚ) : ℝ) * cotangentTermV 23 34    + 
      ((24/34 : ℚ) : ℝ) * cotangentTermV 24 34    + 
      ((25/34 : ℚ) : ℝ) * cotangentTermV 25 34    + 
      ((26/34 : ℚ) : ℝ) * cotangentTermV 26 34    + 
      ((27/34 : ℚ) : ℝ) * cotangentTermV 27 34    + 
      ((28/34 : ℚ) : ℝ) * cotangentTermV 28 34    + 
      ((29/34 : ℚ) : ℝ) * cotangentTermV 29 34    + 
      ((30/34 : ℚ) : ℝ) * cotangentTermV 30 34    + 
      ((31/34 : ℚ) : ℝ) * cotangentTermV 31 34    + 
      ((32/34 : ℚ) : ℝ) * cotangentTermV 32 34    + 
      ((33/34 : ℚ) : ℝ) * cotangentTermV 33 34 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_34]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((1/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((2/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((3/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((4/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((5/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((6/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((7/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((8/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((9/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((10/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((11/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((12/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((13/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((14/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((15/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((16/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((17/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((18/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((19/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((20/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((21/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((22/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((23/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((24/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((25/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((26/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((27/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((28/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((29/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((30/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((31/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((32/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((34 : ℕ) : ℝ)) = ((33/34 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33]
  try ring

def cotangentSumVFormula_35_34_lower : ℚ := -1365675192087649954513 / 54975581388800000000
def cotangentSumVFormula_35_34_upper : ℚ := -1365675190988115670487 / 54975581388800000000
theorem cotangentSumVFormula_35_34_bounds :
  ((cotangentSumVFormula_35_34_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 34 ∧
  cotangentSumVFormula 35 34 ≤ ((cotangentSumVFormula_35_34_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_34_unfold]
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
  rw [cotangentSumVFormula_35_34_lower, cotangentSumVFormula_35_34_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3435_formula_bound :
  (((39583535794561204251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 34 35) ∧
  (vasyuninBEntryFormula 34 35 ≤ ((39585787594376045749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 34 35 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log34 := prim_log_34_bounds
  have b_log35 := prim_log_35_bounds
  have b_Vhk := cotangentSumVFormula_34_35_bounds
  have b_Vkh := cotangentSumVFormula_35_34_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_34_lower, prim_log_34_upper] at b_log34
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [cotangentSumVFormula_34_35_lower, cotangentSumVFormula_34_35_upper] at b_Vhk
  simp only [cotangentSumVFormula_35_34_lower, cotangentSumVFormula_35_34_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_36_unfold :
    cotangentSumVFormula 1 36 =
      ((1/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_1_36_lower : ℚ := -2961943642388255768401 / 109951162777600000000
def cotangentSumVFormula_1_36_upper : ℚ := -2961943640189178606599 / 109951162777600000000
theorem cotangentSumVFormula_1_36_bounds :
  ((cotangentSumVFormula_1_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 36 ∧
  cotangentSumVFormula 1 36 ≤ ((cotangentSumVFormula_1_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_36_unfold]
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
  rw [cotangentSumVFormula_1_36_lower, cotangentSumVFormula_1_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_1_unfold :
    cotangentSumVFormula 36 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_36_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_36_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_36_1_bounds :
  ((cotangentSumVFormula_36_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 1 ∧
  cotangentSumVFormula 36 1 ≤ ((cotangentSumVFormula_36_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_1_unfold]
  rw [cotangentSumVFormula_36_1_lower, cotangentSumVFormula_36_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_136_formula_bound :
  (((2859572403861583043 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 36) ∧
  (vasyuninBEntryFormula 1 36 ≤ ((714910693151662833 / 8796093022208000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_1_36_bounds
  have b_Vkh := cotangentSumVFormula_36_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_1_36_lower, cotangentSumVFormula_1_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_1_lower, cotangentSumVFormula_36_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_36_unfold :
    cotangentSumVFormula 5 36 =
      ((5/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_5_36_lower : ℚ := -243925342383272047569 / 27487790694400000000
def cotangentSumVFormula_5_36_upper : ℚ := -975701367334011419099 / 109951162777600000000
theorem cotangentSumVFormula_5_36_bounds :
  ((cotangentSumVFormula_5_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 36 ∧
  cotangentSumVFormula 5 36 ≤ ((cotangentSumVFormula_5_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_36_unfold]
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
  rw [cotangentSumVFormula_5_36_lower, cotangentSumVFormula_5_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_5_unfold :
    cotangentSumVFormula 36 5 =
      ((1/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_36_5_lower : ℚ := -3134269962581291229457 / 3518437208883200000000
def cotangentSumVFormula_36_5_upper : ℚ := -3134269892212532208043 / 3518437208883200000000
theorem cotangentSumVFormula_36_5_bounds :
  ((cotangentSumVFormula_36_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 5 ∧
  cotangentSumVFormula 36 5 ≤ ((cotangentSumVFormula_36_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_36_5_lower, cotangentSumVFormula_36_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_536_formula_bound :
  (((66200289672320391751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 36) ∧
  (vasyuninBEntryFormula 5 36 ≤ ((66202541472139514499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_5_36_bounds
  have b_Vkh := cotangentSumVFormula_36_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_5_36_lower, cotangentSumVFormula_5_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_5_lower, cotangentSumVFormula_36_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_36_unfold :
    cotangentSumVFormula 7 36 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_7_36_lower : ℚ := -2068423204082095339229 / 439804651110400000000
def cotangentSumVFormula_7_36_upper : ℚ := -2068423195285799973271 / 439804651110400000000
theorem cotangentSumVFormula_7_36_bounds :
  ((cotangentSumVFormula_7_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 36 ∧
  cotangentSumVFormula 7 36 ≤ ((cotangentSumVFormula_7_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_36_unfold]
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
  rw [cotangentSumVFormula_7_36_lower, cotangentSumVFormula_7_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_7_unfold :
    cotangentSumVFormula 36 7 =
      ((1/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_36_7_lower : ℚ := -3267942246185352841291 / 1759218604441600000000
def cotangentSumVFormula_36_7_upper : ℚ := -3267942211000966689959 / 1759218604441600000000
theorem cotangentSumVFormula_36_7_bounds :
  ((cotangentSumVFormula_36_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 7 ∧
  cotangentSumVFormula 36 7 ≤ ((cotangentSumVFormula_36_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_7_unfold]
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
  rw [cotangentSumVFormula_36_7_lower, cotangentSumVFormula_36_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_736_formula_bound :
  (((1907788975140301793 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 36) ∧
  (vasyuninBEntryFormula 7 36 ≤ ((61051499004307014499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_7_36_bounds
  have b_Vkh := cotangentSumVFormula_36_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_7_36_lower, cotangentSumVFormula_7_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_7_lower, cotangentSumVFormula_36_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_36_unfold :
    cotangentSumVFormula 11 36 =
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
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_11_36_lower : ℚ := -2343335633971156747541 / 1759218604441600000000
def cotangentSumVFormula_11_36_upper : ℚ := -2343335598785974502459 / 1759218604441600000000
theorem cotangentSumVFormula_11_36_bounds :
  ((cotangentSumVFormula_11_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 36 ∧
  cotangentSumVFormula 11 36 ≤ ((cotangentSumVFormula_11_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_36_unfold]
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
  rw [cotangentSumVFormula_11_36_lower, cotangentSumVFormula_11_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_11_unfold :
    cotangentSumVFormula 36 11 =
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
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_36_11_lower : ℚ := -2230748134936280966291 / 1759218604441600000000
def cotangentSumVFormula_36_11_upper : ℚ := -2230748099751851064959 / 1759218604441600000000
theorem cotangentSumVFormula_36_11_bounds :
  ((cotangentSumVFormula_36_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 11 ∧
  cotangentSumVFormula 36 11 ≤ ((cotangentSumVFormula_36_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_11_unfold]
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
  rw [cotangentSumVFormula_36_11_lower, cotangentSumVFormula_36_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1136_formula_bound :
  (((107409853557566299127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 36) ∧
  (vasyuninBEntryFormula 11 36 ≤ ((107414357157198513373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_11_36_bounds
  have b_Vkh := cotangentSumVFormula_36_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_11_36_lower, cotangentSumVFormula_11_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_11_lower, cotangentSumVFormula_36_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_36_unfold :
    cotangentSumVFormula 13 36 =
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
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_13_36_lower : ℚ := -1277376809773678151729 / 439804651110400000000
def cotangentSumVFormula_13_36_upper : ℚ := -1277376800977402317021 / 439804651110400000000
theorem cotangentSumVFormula_13_36_bounds :
  ((cotangentSumVFormula_13_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 36 ∧
  cotangentSumVFormula 13 36 ≤ ((cotangentSumVFormula_13_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_36_unfold]
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
  rw [cotangentSumVFormula_13_36_lower, cotangentSumVFormula_13_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_13_unfold :
    cotangentSumVFormula 36 13 =
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
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_36_13_lower : ℚ := 1410513581720014399667 / 879609302220800000000
def cotangentSumVFormula_36_13_upper : ℚ := 705256799656120339229 / 439804651110400000000
theorem cotangentSumVFormula_36_13_bounds :
  ((cotangentSumVFormula_36_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 13 ∧
  cotangentSumVFormula 36 13 ≤ ((cotangentSumVFormula_36_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_13_unfold]
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
  rw [cotangentSumVFormula_36_13_lower, cotangentSumVFormula_36_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1336_formula_bound :
  (((51039730070554298001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 36) ∧
  (vasyuninBEntryFormula 13 36 ≤ ((12760495467592476281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_13_36_bounds
  have b_Vkh := cotangentSumVFormula_36_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_13_36_lower, cotangentSumVFormula_13_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_13_lower, cotangentSumVFormula_36_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_36_unfold :
    cotangentSumVFormula 17 36 =
      ((17/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_17_36_lower : ℚ := 2498974156107120285771 / 439804651110400000000
def cotangentSumVFormula_17_36_upper : ℚ := 2498974164903411745479 / 439804651110400000000
theorem cotangentSumVFormula_17_36_bounds :
  ((cotangentSumVFormula_17_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 36 ∧
  cotangentSumVFormula 17 36 ≤ ((cotangentSumVFormula_17_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_36_unfold]
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
  rw [cotangentSumVFormula_17_36_lower, cotangentSumVFormula_17_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_17_unfold :
    cotangentSumVFormula 36 17 =
      ((2/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_36_17_lower : ℚ := -2371761849596309401729 / 439804651110400000000
def cotangentSumVFormula_36_17_upper : ℚ := -2371761840800178098271 / 439804651110400000000
theorem cotangentSumVFormula_36_17_bounds :
  ((cotangentSumVFormula_36_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 17 ∧
  cotangentSumVFormula 36 17 ≤ ((cotangentSumVFormula_36_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_17_unfold]
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
  rw [cotangentSumVFormula_36_17_lower, cotangentSumVFormula_36_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1736_formula_bound :
  (((47509781180943641751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 36) ∧
  (vasyuninBEntryFormula 17 36 ≤ ((47512032980759014499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_17_36_bounds
  have b_Vkh := cotangentSumVFormula_36_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_17_36_lower, cotangentSumVFormula_17_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_17_lower, cotangentSumVFormula_36_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_36_unfold :
    cotangentSumVFormula 19 36 =
      ((19/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_19_36_lower : ℚ := -1249487082451693177427 / 219902325555200000000
def cotangentSumVFormula_19_36_upper : ℚ := -624743539026778606599 / 109951162777600000000
theorem cotangentSumVFormula_19_36_bounds :
  ((cotangentSumVFormula_19_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 36 ∧
  cotangentSumVFormula 19 36 ≤ ((cotangentSumVFormula_19_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_36_unfold]
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
  rw [cotangentSumVFormula_19_36_lower, cotangentSumVFormula_19_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_19_unfold :
    cotangentSumVFormula 36 19 =
      ((17/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_36_19_lower : ℚ := 2913949859118411692021 / 439804651110400000000
def cotangentSumVFormula_36_19_upper : ℚ := 2913949867914547682979 / 439804651110400000000
theorem cotangentSumVFormula_36_19_bounds :
  ((cotangentSumVFormula_36_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 19 ∧
  cotangentSumVFormula 36 19 ≤ ((cotangentSumVFormula_36_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_19_unfold]
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
  rw [cotangentSumVFormula_36_19_lower, cotangentSumVFormula_36_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1936_formula_bound :
  (((91366471502206736627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 36) ∧
  (vasyuninBEntryFormula 19 36 ≤ ((91370975101836982123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_19_36_bounds
  have b_Vkh := cotangentSumVFormula_36_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_19_36_lower, cotangentSumVFormula_19_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_19_lower, cotangentSumVFormula_36_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_36_unfold :
    cotangentSumVFormula 23 36 =
      ((23/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_23_36_lower : ℚ := 2554753601954830805917 / 879609302220800000000
def cotangentSumVFormula_23_36_upper : ℚ := 2554753619547392631583 / 879609302220800000000
theorem cotangentSumVFormula_23_36_bounds :
  ((cotangentSumVFormula_23_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 36 ∧
  cotangentSumVFormula 23 36 ≤ ((cotangentSumVFormula_23_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_36_unfold]
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
  rw [cotangentSumVFormula_23_36_lower, cotangentSumVFormula_23_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_23_unfold :
    cotangentSumVFormula 36 23 =
      ((13/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((14/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_36_23_lower : ℚ := -2033603874296813104457 / 3518437208883200000000
def cotangentSumVFormula_36_23_upper : ℚ := -2033603803927415020543 / 3518437208883200000000
theorem cotangentSumVFormula_36_23_bounds :
  ((cotangentSumVFormula_36_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 23 ∧
  cotangentSumVFormula 36 23 ≤ ((cotangentSumVFormula_36_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_23_unfold]
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
  rw [cotangentSumVFormula_36_23_lower, cotangentSumVFormula_36_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2336_formula_bound :
  (((83278979529384549127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 36) ∧
  (vasyuninBEntryFormula 23 36 ≤ ((83283483129014763373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_23_36_bounds
  have b_Vkh := cotangentSumVFormula_36_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_23_36_lower, cotangentSumVFormula_23_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_23_lower, cotangentSumVFormula_36_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_25_36_unfold :
    cotangentSumVFormula 25 36 =
      ((25/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_25_36_lower : ℚ := 1171667799393034712167 / 879609302220800000000
def cotangentSumVFormula_25_36_upper : ℚ := 1171667816985580912833 / 879609302220800000000
theorem cotangentSumVFormula_25_36_bounds :
  ((cotangentSumVFormula_25_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 36 ∧
  cotangentSumVFormula 25 36 ≤ ((cotangentSumVFormula_25_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_36_unfold]
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
  rw [cotangentSumVFormula_25_36_lower, cotangentSumVFormula_25_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_25_unfold :
    cotangentSumVFormula 36 25 =
      ((11/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((22/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((19/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((24/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((21/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((12/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((17/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((14/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 36 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_36_25_lower : ℚ := 2321312897179799502459 / 1759218604441600000000
def cotangentSumVFormula_36_25_upper : ℚ := 2321312932364475497541 / 1759218604441600000000
theorem cotangentSumVFormula_36_25_bounds :
  ((cotangentSumVFormula_36_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 25 ∧
  cotangentSumVFormula 36 25 ≤ ((cotangentSumVFormula_36_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_25_unfold]
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
  rw [cotangentSumVFormula_36_25_lower, cotangentSumVFormula_36_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2536_formula_bound :
  (((80761294139364611627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 36) ∧
  (vasyuninBEntryFormula 25 36 ≤ ((80765797738994482123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_25_36_bounds
  have b_Vkh := cotangentSumVFormula_36_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_25_36_lower, cotangentSumVFormula_25_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_25_lower, cotangentSumVFormula_36_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_29_36_unfold :
    cotangentSumVFormula 29 36 =
      ((29/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 29 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_29_36_lower : ℚ := 2068423195285831223271 / 439804651110400000000
def cotangentSumVFormula_29_36_upper : ℚ := 2068423204082092995479 / 439804651110400000000
theorem cotangentSumVFormula_29_36_bounds :
  ((cotangentSumVFormula_29_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 29 36 ∧
  cotangentSumVFormula 29 36 ≤ ((cotangentSumVFormula_29_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_29_36_unfold]
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
  rw [cotangentSumVFormula_29_36_lower, cotangentSumVFormula_29_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_29_unfold :
    cotangentSumVFormula 36 29 =
      ((7/29 : ℚ) : ℝ) * cotangentTermV 1 29    + 
      ((14/29 : ℚ) : ℝ) * cotangentTermV 2 29    + 
      ((21/29 : ℚ) : ℝ) * cotangentTermV 3 29    + 
      ((28/29 : ℚ) : ℝ) * cotangentTermV 4 29    + 
      ((6/29 : ℚ) : ℝ) * cotangentTermV 5 29    + 
      ((13/29 : ℚ) : ℝ) * cotangentTermV 6 29    + 
      ((20/29 : ℚ) : ℝ) * cotangentTermV 7 29    + 
      ((27/29 : ℚ) : ℝ) * cotangentTermV 8 29    + 
      ((5/29 : ℚ) : ℝ) * cotangentTermV 9 29    + 
      ((12/29 : ℚ) : ℝ) * cotangentTermV 10 29    + 
      ((19/29 : ℚ) : ℝ) * cotangentTermV 11 29    + 
      ((26/29 : ℚ) : ℝ) * cotangentTermV 12 29    + 
      ((4/29 : ℚ) : ℝ) * cotangentTermV 13 29    + 
      ((11/29 : ℚ) : ℝ) * cotangentTermV 14 29    + 
      ((18/29 : ℚ) : ℝ) * cotangentTermV 15 29    + 
      ((25/29 : ℚ) : ℝ) * cotangentTermV 16 29    + 
      ((3/29 : ℚ) : ℝ) * cotangentTermV 17 29    + 
      ((10/29 : ℚ) : ℝ) * cotangentTermV 18 29    + 
      ((17/29 : ℚ) : ℝ) * cotangentTermV 19 29    + 
      ((24/29 : ℚ) : ℝ) * cotangentTermV 20 29    + 
      ((2/29 : ℚ) : ℝ) * cotangentTermV 21 29    + 
      ((9/29 : ℚ) : ℝ) * cotangentTermV 22 29    + 
      ((16/29 : ℚ) : ℝ) * cotangentTermV 23 29    + 
      ((23/29 : ℚ) : ℝ) * cotangentTermV 24 29    + 
      ((1/29 : ℚ) : ℝ) * cotangentTermV 25 29    + 
      ((8/29 : ℚ) : ℝ) * cotangentTermV 26 29    + 
      ((15/29 : ℚ) : ℝ) * cotangentTermV 27 29    + 
      ((22/29 : ℚ) : ℝ) * cotangentTermV 28 29 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_29]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((7/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((14/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((21/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((28/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((6/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((13/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((20/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((27/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((5/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((12/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((19/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((26/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((4/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((11/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((18/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((25/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((3/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((10/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((17/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((24/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((2/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((9/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((16/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((23/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((1/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((8/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((15/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 36 : ℕ) : ℝ) / ((29 : ℕ) : ℝ)) = ((22/29 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28]
  try ring

def cotangentSumVFormula_36_29_lower : ℚ := -3291565442321297372541 / 1759218604441600000000
def cotangentSumVFormula_36_29_upper : ℚ := -3291565407136465127459 / 1759218604441600000000
theorem cotangentSumVFormula_36_29_bounds :
  ((cotangentSumVFormula_36_29_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 29 ∧
  cotangentSumVFormula 36 29 ≤ ((cotangentSumVFormula_36_29_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_29_unfold]
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
  rw [cotangentSumVFormula_36_29_lower, cotangentSumVFormula_36_29_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2936_formula_bound :
  (((4821358637219191547 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 29 36) ∧
  (vasyuninBEntryFormula 29 36 ≤ ((38573120897568420749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 29 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log29 := log_29_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_29_36_bounds
  have b_Vkh := cotangentSumVFormula_36_29_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_29_lower, log_29_upper] at b_log29
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_29_36_lower, cotangentSumVFormula_29_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_29_lower, cotangentSumVFormula_36_29_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_31_36_unfold :
    cotangentSumVFormula 31 36 =
      ((31/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((35/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 31 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_31_36_lower : ℚ := 975701367334020012849 / 109951162777600000000
def cotangentSumVFormula_31_36_upper : ℚ := 975701369533084674651 / 109951162777600000000
theorem cotangentSumVFormula_31_36_bounds :
  ((cotangentSumVFormula_31_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 31 36 ∧
  cotangentSumVFormula 31 36 ≤ ((cotangentSumVFormula_31_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_31_36_unfold]
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
  rw [cotangentSumVFormula_31_36_lower, cotangentSumVFormula_31_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_31_unfold :
    cotangentSumVFormula 36 31 =
      ((5/31 : ℚ) : ℝ) * cotangentTermV 1 31    + 
      ((10/31 : ℚ) : ℝ) * cotangentTermV 2 31    + 
      ((15/31 : ℚ) : ℝ) * cotangentTermV 3 31    + 
      ((20/31 : ℚ) : ℝ) * cotangentTermV 4 31    + 
      ((25/31 : ℚ) : ℝ) * cotangentTermV 5 31    + 
      ((30/31 : ℚ) : ℝ) * cotangentTermV 6 31    + 
      ((4/31 : ℚ) : ℝ) * cotangentTermV 7 31    + 
      ((9/31 : ℚ) : ℝ) * cotangentTermV 8 31    + 
      ((14/31 : ℚ) : ℝ) * cotangentTermV 9 31    + 
      ((19/31 : ℚ) : ℝ) * cotangentTermV 10 31    + 
      ((24/31 : ℚ) : ℝ) * cotangentTermV 11 31    + 
      ((29/31 : ℚ) : ℝ) * cotangentTermV 12 31    + 
      ((3/31 : ℚ) : ℝ) * cotangentTermV 13 31    + 
      ((8/31 : ℚ) : ℝ) * cotangentTermV 14 31    + 
      ((13/31 : ℚ) : ℝ) * cotangentTermV 15 31    + 
      ((18/31 : ℚ) : ℝ) * cotangentTermV 16 31    + 
      ((23/31 : ℚ) : ℝ) * cotangentTermV 17 31    + 
      ((28/31 : ℚ) : ℝ) * cotangentTermV 18 31    + 
      ((2/31 : ℚ) : ℝ) * cotangentTermV 19 31    + 
      ((7/31 : ℚ) : ℝ) * cotangentTermV 20 31    + 
      ((12/31 : ℚ) : ℝ) * cotangentTermV 21 31    + 
      ((17/31 : ℚ) : ℝ) * cotangentTermV 22 31    + 
      ((22/31 : ℚ) : ℝ) * cotangentTermV 23 31    + 
      ((27/31 : ℚ) : ℝ) * cotangentTermV 24 31    + 
      ((1/31 : ℚ) : ℝ) * cotangentTermV 25 31    + 
      ((6/31 : ℚ) : ℝ) * cotangentTermV 26 31    + 
      ((11/31 : ℚ) : ℝ) * cotangentTermV 27 31    + 
      ((16/31 : ℚ) : ℝ) * cotangentTermV 28 31    + 
      ((21/31 : ℚ) : ℝ) * cotangentTermV 29 31    + 
      ((26/31 : ℚ) : ℝ) * cotangentTermV 30 31 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_31]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((5/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((10/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((15/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((20/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((25/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((30/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((4/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((9/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((14/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((19/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((24/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((29/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((3/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((8/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((13/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((18/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((23/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((28/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((2/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((7/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((12/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((17/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((22/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((27/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((1/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((6/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((11/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((16/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((21/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 36 : ℕ) : ℝ) / ((31 : ℕ) : ℝ)) = ((26/31 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30]
  try ring

def cotangentSumVFormula_36_31_lower : ℚ := -2754431825625420339229 / 439804651110400000000
def cotangentSumVFormula_36_31_upper : ℚ := -2754431816829160910771 / 439804651110400000000
theorem cotangentSumVFormula_36_31_bounds :
  ((cotangentSumVFormula_36_31_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 31 ∧
  cotangentSumVFormula 36 31 ≤ ((cotangentSumVFormula_36_31_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_31_unfold]
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
  rw [cotangentSumVFormula_36_31_lower, cotangentSumVFormula_36_31_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3136_formula_bound :
  (((76181265598394455377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 31 36) ∧
  (vasyuninBEntryFormula 31 36 ≤ ((76185769198024419623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 31 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log31 := log_31_certified_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_31_36_bounds
  have b_Vkh := cotangentSumVFormula_36_31_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_31_lower, log_31_upper] at b_log31
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_31_36_lower, cotangentSumVFormula_31_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_31_lower, cotangentSumVFormula_36_31_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_35_36_unfold :
    cotangentSumVFormula 35 36 =
      ((35/36 : ℚ) : ℝ) * cotangentTermV 1 36    + 
      ((34/36 : ℚ) : ℝ) * cotangentTermV 2 36    + 
      ((33/36 : ℚ) : ℝ) * cotangentTermV 3 36    + 
      ((32/36 : ℚ) : ℝ) * cotangentTermV 4 36    + 
      ((31/36 : ℚ) : ℝ) * cotangentTermV 5 36    + 
      ((30/36 : ℚ) : ℝ) * cotangentTermV 6 36    + 
      ((29/36 : ℚ) : ℝ) * cotangentTermV 7 36    + 
      ((28/36 : ℚ) : ℝ) * cotangentTermV 8 36    + 
      ((27/36 : ℚ) : ℝ) * cotangentTermV 9 36    + 
      ((26/36 : ℚ) : ℝ) * cotangentTermV 10 36    + 
      ((25/36 : ℚ) : ℝ) * cotangentTermV 11 36    + 
      ((24/36 : ℚ) : ℝ) * cotangentTermV 12 36    + 
      ((23/36 : ℚ) : ℝ) * cotangentTermV 13 36    + 
      ((22/36 : ℚ) : ℝ) * cotangentTermV 14 36    + 
      ((21/36 : ℚ) : ℝ) * cotangentTermV 15 36    + 
      ((20/36 : ℚ) : ℝ) * cotangentTermV 16 36    + 
      ((19/36 : ℚ) : ℝ) * cotangentTermV 17 36    + 
      ((18/36 : ℚ) : ℝ) * cotangentTermV 18 36    + 
      ((17/36 : ℚ) : ℝ) * cotangentTermV 19 36    + 
      ((16/36 : ℚ) : ℝ) * cotangentTermV 20 36    + 
      ((15/36 : ℚ) : ℝ) * cotangentTermV 21 36    + 
      ((14/36 : ℚ) : ℝ) * cotangentTermV 22 36    + 
      ((13/36 : ℚ) : ℝ) * cotangentTermV 23 36    + 
      ((12/36 : ℚ) : ℝ) * cotangentTermV 24 36    + 
      ((11/36 : ℚ) : ℝ) * cotangentTermV 25 36    + 
      ((10/36 : ℚ) : ℝ) * cotangentTermV 26 36    + 
      ((9/36 : ℚ) : ℝ) * cotangentTermV 27 36    + 
      ((8/36 : ℚ) : ℝ) * cotangentTermV 28 36    + 
      ((7/36 : ℚ) : ℝ) * cotangentTermV 29 36    + 
      ((6/36 : ℚ) : ℝ) * cotangentTermV 30 36    + 
      ((5/36 : ℚ) : ℝ) * cotangentTermV 31 36    + 
      ((4/36 : ℚ) : ℝ) * cotangentTermV 32 36    + 
      ((3/36 : ℚ) : ℝ) * cotangentTermV 33 36    + 
      ((2/36 : ℚ) : ℝ) * cotangentTermV 34 36    + 
      ((1/36 : ℚ) : ℝ) * cotangentTermV 35 36 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_36]
  have hf_1 : Int.fract (((1 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((35/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((34/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((33/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((32/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((31/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((30/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((29/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((28/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((27/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((26/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((25/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((24/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((23/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((22/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((21/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((20/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((19/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((18/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((17/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((16/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((15/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((14/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((13/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((12/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((11/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((10/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((9/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((8/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((7/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((6/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((5/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((4/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((3/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((2/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 35 : ℕ) : ℝ) / ((36 : ℕ) : ℝ)) = ((1/36 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35]
  try ring

def cotangentSumVFormula_35_36_lower : ℚ := 2961943640189191887849 / 109951162777600000000
def cotangentSumVFormula_35_36_upper : ℚ := 2961943642388251080901 / 109951162777600000000
theorem cotangentSumVFormula_35_36_bounds :
  ((cotangentSumVFormula_35_36_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 35 36 ∧
  cotangentSumVFormula 35 36 ≤ ((cotangentSumVFormula_35_36_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_35_36_unfold]
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
  rw [cotangentSumVFormula_35_36_lower, cotangentSumVFormula_35_36_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_36_35_unfold :
    cotangentSumVFormula 36 35 =
      ((1/35 : ℚ) : ℝ) * cotangentTermV 1 35    + 
      ((2/35 : ℚ) : ℝ) * cotangentTermV 2 35    + 
      ((3/35 : ℚ) : ℝ) * cotangentTermV 3 35    + 
      ((4/35 : ℚ) : ℝ) * cotangentTermV 4 35    + 
      ((5/35 : ℚ) : ℝ) * cotangentTermV 5 35    + 
      ((6/35 : ℚ) : ℝ) * cotangentTermV 6 35    + 
      ((7/35 : ℚ) : ℝ) * cotangentTermV 7 35    + 
      ((8/35 : ℚ) : ℝ) * cotangentTermV 8 35    + 
      ((9/35 : ℚ) : ℝ) * cotangentTermV 9 35    + 
      ((10/35 : ℚ) : ℝ) * cotangentTermV 10 35    + 
      ((11/35 : ℚ) : ℝ) * cotangentTermV 11 35    + 
      ((12/35 : ℚ) : ℝ) * cotangentTermV 12 35    + 
      ((13/35 : ℚ) : ℝ) * cotangentTermV 13 35    + 
      ((14/35 : ℚ) : ℝ) * cotangentTermV 14 35    + 
      ((15/35 : ℚ) : ℝ) * cotangentTermV 15 35    + 
      ((16/35 : ℚ) : ℝ) * cotangentTermV 16 35    + 
      ((17/35 : ℚ) : ℝ) * cotangentTermV 17 35    + 
      ((18/35 : ℚ) : ℝ) * cotangentTermV 18 35    + 
      ((19/35 : ℚ) : ℝ) * cotangentTermV 19 35    + 
      ((20/35 : ℚ) : ℝ) * cotangentTermV 20 35    + 
      ((21/35 : ℚ) : ℝ) * cotangentTermV 21 35    + 
      ((22/35 : ℚ) : ℝ) * cotangentTermV 22 35    + 
      ((23/35 : ℚ) : ℝ) * cotangentTermV 23 35    + 
      ((24/35 : ℚ) : ℝ) * cotangentTermV 24 35    + 
      ((25/35 : ℚ) : ℝ) * cotangentTermV 25 35    + 
      ((26/35 : ℚ) : ℝ) * cotangentTermV 26 35    + 
      ((27/35 : ℚ) : ℝ) * cotangentTermV 27 35    + 
      ((28/35 : ℚ) : ℝ) * cotangentTermV 28 35    + 
      ((29/35 : ℚ) : ℝ) * cotangentTermV 29 35    + 
      ((30/35 : ℚ) : ℝ) * cotangentTermV 30 35    + 
      ((31/35 : ℚ) : ℝ) * cotangentTermV 31 35    + 
      ((32/35 : ℚ) : ℝ) * cotangentTermV 32 35    + 
      ((33/35 : ℚ) : ℝ) * cotangentTermV 33 35    + 
      ((34/35 : ℚ) : ℝ) * cotangentTermV 34 35 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_35]
  have hf_1 : Int.fract (((1 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((1/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((2/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((3/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((4/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((5/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((6/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((7/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((8/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((9/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((10/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((11/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((12/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((13/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((14/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((15/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((16/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((17/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((18/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((19/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((20/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((21/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((22/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((23/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((24/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((25/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((26/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((27/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((28/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((29/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((30/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((31/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((32/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((33/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 36 : ℕ) : ℝ) / ((35 : ℕ) : ℝ)) = ((34/35 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34]
  try ring

def cotangentSumVFormula_36_35_lower : ℚ := -2846146742160322174651 / 109951162777600000000
def cotangentSumVFormula_36_35_upper : ℚ := -2846146739961249700349 / 109951162777600000000
theorem cotangentSumVFormula_36_35_bounds :
  ((cotangentSumVFormula_36_35_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 36 35 ∧
  cotangentSumVFormula 36 35 ≤ ((cotangentSumVFormula_36_35_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_36_35_unfold]
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
  rw [cotangentSumVFormula_36_35_lower, cotangentSumVFormula_36_35_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_3536_formula_bound :
  (((76996941903761174127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 35 36) ∧
  (vasyuninBEntryFormula 35 36 ≤ ((77001445503390950873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 35 36 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log35 := prim_log_35_bounds
  have b_log36 := prim_log_36_bounds
  have b_Vhk := cotangentSumVFormula_35_36_bounds
  have b_Vkh := cotangentSumVFormula_36_35_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_35_lower, prim_log_35_upper] at b_log35
  simp only [prim_log_36_lower, prim_log_36_upper] at b_log36
  simp only [cotangentSumVFormula_35_36_lower, cotangentSumVFormula_35_36_upper] at b_Vhk
  simp only [cotangentSumVFormula_36_35_lower, cotangentSumVFormula_36_35_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_37_unfold :
    cotangentSumVFormula 1 37 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 1 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_1_37_lower : ℚ := -1539356630453005423263 / 54975581388800000000
def cotangentSumVFormula_1_37_upper : ℚ := -769678314676734983681 / 27487790694400000000
theorem cotangentSumVFormula_1_37_bounds :
  ((cotangentSumVFormula_1_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 37 ∧
  cotangentSumVFormula 1 37 ≤ ((cotangentSumVFormula_1_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_37_unfold]
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
  rw [cotangentSumVFormula_1_37_lower, cotangentSumVFormula_1_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_1_unfold :
    cotangentSumVFormula 37 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_37_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_37_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_37_1_bounds :
  ((cotangentSumVFormula_37_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 1 ∧
  cotangentSumVFormula 37 1 ≤ ((cotangentSumVFormula_37_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_1_unfold]
  rw [cotangentSumVFormula_37_1_lower, cotangentSumVFormula_37_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_137_formula_bound :
  (((1397607552341533709 / 17592186044416000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 37) ∧
  (vasyuninBEntryFormula 1 37 ≤ ((2795285473428010707 / 35184372088832000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_37_bounds
  have b_Vkh := cotangentSumVFormula_37_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_1_37_lower, cotangentSumVFormula_1_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_1_lower, cotangentSumVFormula_37_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_37_unfold :
    cotangentSumVFormula 2 37 =
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
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 2 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_2_37_lower : ℚ := -2215734768764665143401 / 109951162777600000000
def cotangentSumVFormula_2_37_upper : ℚ := -2215734766565595794099 / 109951162777600000000
theorem cotangentSumVFormula_2_37_bounds :
  ((cotangentSumVFormula_2_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 37 ∧
  cotangentSumVFormula 2 37 ≤ ((cotangentSumVFormula_2_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_37_unfold]
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
  rw [cotangentSumVFormula_2_37_lower, cotangentSumVFormula_2_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_2_unfold :
    cotangentSumVFormula 37 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_37_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_37_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_37_2_bounds :
  ((cotangentSumVFormula_37_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 2 ∧
  cotangentSumVFormula 37 2 ≤ ((cotangentSumVFormula_37_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_37_2_lower, cotangentSumVFormula_37_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_237_formula_bound :
  (((39379930719457688063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 37) ∧
  (vasyuninBEntryFormula 2 37 ≤ ((39381056619370499437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_37_bounds
  have b_Vkh := cotangentSumVFormula_37_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_2_37_lower, cotangentSumVFormula_2_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_2_lower, cotangentSumVFormula_37_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
