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

theorem cotangentSumVFormula_3_37_unfold :
    cotangentSumVFormula 3 37 =
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
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 3 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_3_37_lower : ℚ := -3408461111432785364927 / 219902325555200000000
def cotangentSumVFormula_3_37_upper : ℚ := -3408461107034641978823 / 219902325555200000000
theorem cotangentSumVFormula_3_37_bounds :
  ((cotangentSumVFormula_3_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 37 ∧
  cotangentSumVFormula 3 37 ≤ ((cotangentSumVFormula_3_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_37_unfold]
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
  rw [cotangentSumVFormula_3_37_lower, cotangentSumVFormula_3_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_3_unfold :
    cotangentSumVFormula 37 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_37_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_37_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_37_3_bounds :
  ((cotangentSumVFormula_37_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 3 ∧
  cotangentSumVFormula 37 3 ≤ ((cotangentSumVFormula_37_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_37_3_lower, cotangentSumVFormula_37_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_337_formula_bound :
  (((72558530783559235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 37) ∧
  (vasyuninBEntryFormula 3 37 ≤ ((72560782583381139499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_37_bounds
  have b_Vkh := cotangentSumVFormula_37_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_3_37_lower, cotangentSumVFormula_3_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_3_lower, cotangentSumVFormula_37_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_37_unfold :
    cotangentSumVFormula 4 37 =
      ((4/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 4 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_4_37_lower : ℚ := -2665657190505848646177 / 219902325555200000000
def cotangentSumVFormula_4_37_upper : ℚ := -2665657186107705260073 / 219902325555200000000
theorem cotangentSumVFormula_4_37_bounds :
  ((cotangentSumVFormula_4_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 37 ∧
  cotangentSumVFormula 4 37 ≤ ((cotangentSumVFormula_4_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_37_unfold]
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
  rw [cotangentSumVFormula_4_37_lower, cotangentSumVFormula_4_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_4_unfold :
    cotangentSumVFormula 37 4 =
      ((1/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((3/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_37_4_lower : ℚ := -1759218639625974041957 / 3518437208883200000000
def cotangentSumVFormula_37_4_upper : ℚ := -1759218569257223614293 / 3518437208883200000000
theorem cotangentSumVFormula_37_4_bounds :
  ((cotangentSumVFormula_37_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 4 ∧
  cotangentSumVFormula 37 4 ≤ ((cotangentSumVFormula_37_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_37_4_lower, cotangentSumVFormula_37_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_437_formula_bound :
  (((136381806483801986627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 37) ∧
  (vasyuninBEntryFormula 4 37 ≤ ((136386310083441513373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_37_bounds
  have b_Vkh := cotangentSumVFormula_37_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_4_37_lower, cotangentSumVFormula_4_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_4_lower, cotangentSumVFormula_37_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_37_unfold :
    cotangentSumVFormula 5 37 =
      ((5/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 5 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_5_37_lower : ℚ := -2247747601022716614927 / 219902325555200000000
def cotangentSumVFormula_5_37_upper : ℚ := -2247747596624577916323 / 219902325555200000000
theorem cotangentSumVFormula_5_37_bounds :
  ((cotangentSumVFormula_5_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 37 ∧
  cotangentSumVFormula 5 37 ≤ ((cotangentSumVFormula_5_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_37_unfold]
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
  rw [cotangentSumVFormula_5_37_lower, cotangentSumVFormula_5_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_5_unfold :
    cotangentSumVFormula 37 5 =
      ((2/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_37_5_lower : ℚ := -2260935825867423195031 / 28147497671065600000000
def cotangentSumVFormula_37_5_upper : ℚ := -2260935262917351804969 / 28147497671065600000000
theorem cotangentSumVFormula_37_5_bounds :
  ((cotangentSumVFormula_37_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 5 ∧
  cotangentSumVFormula 37 5 ≤ ((cotangentSumVFormula_37_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_37_5_lower, cotangentSumVFormula_37_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_537_formula_bound :
  (((8088378777272004047 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 37) ∧
  (vasyuninBEntryFormula 5 37 ≤ ((32354641008997218187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_37_bounds
  have b_Vkh := cotangentSumVFormula_37_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_5_37_lower, cotangentSumVFormula_5_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_5_lower, cotangentSumVFormula_37_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_37_unfold :
    cotangentSumVFormula 6 37 =
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
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 6 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_6_37_lower : ℚ := -3141951301369710182979 / 439804651110400000000
def cotangentSumVFormula_6_37_upper : ℚ := -3141951292573434348271 / 439804651110400000000
theorem cotangentSumVFormula_6_37_bounds :
  ((cotangentSumVFormula_6_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 37 ∧
  cotangentSumVFormula 6 37 ≤ ((cotangentSumVFormula_6_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_37_unfold]
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
  rw [cotangentSumVFormula_6_37_lower, cotangentSumVFormula_6_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_6_unfold :
    cotangentSumVFormula 37 6 =
      ((1/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((5/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_37_6_lower : ℚ := -2369932465546953622541 / 1759218604441600000000
def cotangentSumVFormula_37_6_upper : ℚ := -2369932430362564346209 / 1759218604441600000000
theorem cotangentSumVFormula_37_6_bounds :
  ((cotangentSumVFormula_37_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 6 ∧
  cotangentSumVFormula 37 6 ≤ ((cotangentSumVFormula_37_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_6_unfold]
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
  rw [cotangentSumVFormula_37_6_lower, cotangentSumVFormula_37_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_637_formula_bound :
  (((124202619491118205377 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 37) ∧
  (vasyuninBEntryFormula 6 37 ≤ ((124207123090753357123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_37_bounds
  have b_Vkh := cotangentSumVFormula_37_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_6_37_lower, cotangentSumVFormula_6_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_6_lower, cotangentSumVFormula_37_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_37_unfold :
    cotangentSumVFormula 7 37 =
      ((7/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 7 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_7_37_lower : ℚ := -2796337024865646901729 / 439804651110400000000
def cotangentSumVFormula_7_37_upper : ℚ := -2796337016069371848271 / 439804651110400000000
theorem cotangentSumVFormula_7_37_bounds :
  ((cotangentSumVFormula_7_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 37 ∧
  cotangentSumVFormula 7 37 ≤ ((cotangentSumVFormula_7_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_37_unfold]
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
  rw [cotangentSumVFormula_7_37_lower, cotangentSumVFormula_7_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_7_unfold :
    cotangentSumVFormula 37 7 =
      ((2/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_37_7_lower : ℚ := -269592303162212526729 / 439804651110400000000
def cotangentSumVFormula_37_7_upper : ℚ := -539184588732231587167 / 879609302220800000000
theorem cotangentSumVFormula_37_7_bounds :
  ((cotangentSumVFormula_37_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 7 ∧
  cotangentSumVFormula 37 7 ≤ ((cotangentSumVFormula_37_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_7_unfold]
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
  rw [cotangentSumVFormula_37_7_lower, cotangentSumVFormula_37_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_737_formula_bound :
  (((119192190080968017877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 37) ∧
  (vasyuninBEntryFormula 7 37 ≤ ((119196693680601919623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_7_37_bounds
  have b_Vkh := cotangentSumVFormula_37_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_7_37_lower, cotangentSumVFormula_7_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_7_lower, cotangentSumVFormula_37_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_37_unfold :
    cotangentSumVFormula 8 37 =
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
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 8 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_8_37_lower : ℚ := -671831399940639362151 / 109951162777600000000
def cotangentSumVFormula_8_37_upper : ℚ := -671831397741572356599 / 109951162777600000000
theorem cotangentSumVFormula_8_37_bounds :
  ((cotangentSumVFormula_8_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 37 ∧
  cotangentSumVFormula 8 37 ≤ ((cotangentSumVFormula_8_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_37_unfold]
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
  rw [cotangentSumVFormula_8_37_lower, cotangentSumVFormula_8_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_8_unfold :
    cotangentSumVFormula 37 8 =
      ((5/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_37_8_lower : ℚ := 728692187546585439959 / 1759218604441600000000
def cotangentSumVFormula_37_8_upper : ℚ := 728692222730973935041 / 1759218604441600000000
theorem cotangentSumVFormula_37_8_bounds :
  ((cotangentSumVFormula_37_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 8 ∧
  cotangentSumVFormula 37 8 ≤ ((cotangentSumVFormula_37_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_8_unfold]
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
  rw [cotangentSumVFormula_37_8_lower, cotangentSumVFormula_37_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_837_formula_bound :
  (((114914245348517799127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 37) ∧
  (vasyuninBEntryFormula 8 37 ≤ ((114918748948150638373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_8_37_bounds
  have b_Vkh := cotangentSumVFormula_37_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_8_37_lower, cotangentSumVFormula_8_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_8_lower, cotangentSumVFormula_37_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_37_unfold :
    cotangentSumVFormula 9 37 =
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
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 9 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_9_37_lower : ℚ := -2986691804981180185041 / 1759218604441600000000
def cotangentSumVFormula_9_37_upper : ℚ := -2986691769796032314959 / 1759218604441600000000
theorem cotangentSumVFormula_9_37_bounds :
  ((cotangentSumVFormula_9_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 37 ∧
  cotangentSumVFormula 9 37 ≤ ((cotangentSumVFormula_9_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_37_unfold]
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
  rw [cotangentSumVFormula_9_37_lower, cotangentSumVFormula_9_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_9_unfold :
    cotangentSumVFormula 37 9 =
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
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_37_9_lower : ℚ := -1324275640802612526729 / 439804651110400000000
def cotangentSumVFormula_37_9_upper : ℚ := -82767227000406858681 / 27487790694400000000
theorem cotangentSumVFormula_37_9_bounds :
  ((cotangentSumVFormula_37_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 9 ∧
  cotangentSumVFormula 37 9 ≤ ((cotangentSumVFormula_37_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_9_unfold]
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
  rw [cotangentSumVFormula_37_9_lower, cotangentSumVFormula_37_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_937_formula_bound :
  (((112250026909257736627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 37) ∧
  (vasyuninBEntryFormula 9 37 ≤ ((112254530508890607123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_9_37_bounds
  have b_Vkh := cotangentSumVFormula_37_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_9_37_lower, cotangentSumVFormula_9_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_9_lower, cotangentSumVFormula_37_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_37_unfold :
    cotangentSumVFormula 10 37 =
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
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 10 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_10_37_lower : ℚ := -937107918655807239927 / 219902325555200000000
def cotangentSumVFormula_10_37_upper : ℚ := -937107914257676353823 / 219902325555200000000
theorem cotangentSumVFormula_10_37_bounds :
  ((cotangentSumVFormula_10_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 37 ∧
  cotangentSumVFormula 10 37 ≤ ((cotangentSumVFormula_10_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_37_unfold]
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
  rw [cotangentSumVFormula_10_37_lower, cotangentSumVFormula_10_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_10_unfold :
    cotangentSumVFormula 37 10 =
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
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_37_10_lower : ℚ := 2003802120016315801793 / 3518437208883200000000
def cotangentSumVFormula_37_10_upper : ℚ := 2003802190385117791957 / 3518437208883200000000
theorem cotangentSumVFormula_37_10_bounds :
  ((cotangentSumVFormula_37_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 10 ∧
  cotangentSumVFormula 37 10 ≤ ((cotangentSumVFormula_37_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_10_unfold]
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
  rw [cotangentSumVFormula_37_10_lower, cotangentSumVFormula_37_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1037_formula_bound :
  (((54049265881766016751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 37) ∧
  (vasyuninBEntryFormula 10 37 ≤ ((13512879420395476281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_10_37_bounds
  have b_Vkh := cotangentSumVFormula_37_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_10_37_lower, cotangentSumVFormula_10_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_10_lower, cotangentSumVFormula_37_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_37_unfold :
    cotangentSumVFormula 11 37 =
      ((11/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 11 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_11_37_lower : ℚ := -3510966508737227060041 / 1759218604441600000000
def cotangentSumVFormula_11_37_upper : ℚ := -3510966473552110439959 / 1759218604441600000000
theorem cotangentSumVFormula_11_37_bounds :
  ((cotangentSumVFormula_11_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 37 ∧
  cotangentSumVFormula 11 37 ≤ ((cotangentSumVFormula_11_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_37_unfold]
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
  rw [cotangentSumVFormula_11_37_lower, cotangentSumVFormula_11_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_11_unfold :
    cotangentSumVFormula 37 11 =
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
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_37_11_lower : ℚ := -3098045053564121698207 / 3518437208883200000000
def cotangentSumVFormula_37_11_upper : ℚ := -3098044983195265801793 / 3518437208883200000000
theorem cotangentSumVFormula_37_11_bounds :
  ((cotangentSumVFormula_37_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 11 ∧
  cotangentSumVFormula 37 11 ≤ ((cotangentSumVFormula_37_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_11_unfold]
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
  rw [cotangentSumVFormula_37_11_lower, cotangentSumVFormula_37_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1137_formula_bound :
  (((105144156413661799127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 37) ∧
  (vasyuninBEntryFormula 11 37 ≤ ((105148660013293607123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_11_37_bounds
  have b_Vkh := cotangentSumVFormula_37_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_11_37_lower, cotangentSumVFormula_11_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_11_lower, cotangentSumVFormula_37_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_12_37_unfold :
    cotangentSumVFormula 12 37 =
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
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 12 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_12_37_lower : ℚ := 2333917607301461274667 / 879609302220800000000
def cotangentSumVFormula_12_37_upper : ℚ := 2333917624894038725333 / 879609302220800000000
theorem cotangentSumVFormula_12_37_bounds :
  ((cotangentSumVFormula_12_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 37 ∧
  cotangentSumVFormula 12 37 ≤ ((cotangentSumVFormula_12_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_37_unfold]
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
  rw [cotangentSumVFormula_12_37_lower, cotangentSumVFormula_12_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_12_unfold :
    cotangentSumVFormula 37 12 =
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
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_37_12_lower : ℚ := -34372459555962836111 / 6871947673600000000
def cotangentSumVFormula_37_12_upper : ℚ := -1099918701392752135073 / 219902325555200000000
theorem cotangentSumVFormula_37_12_bounds :
  ((cotangentSumVFormula_37_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 12 ∧
  cotangentSumVFormula 37 12 ≤ ((cotangentSumVFormula_37_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_12_unfold]
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
  rw [cotangentSumVFormula_37_12_lower, cotangentSumVFormula_37_12_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1237_formula_bound :
  (((103966334572716924127 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 12 37) ∧
  (vasyuninBEntryFormula 12 37 ≤ ((103970838172348700873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 12 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log12 := prim_log_12_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_12_37_bounds
  have b_Vkh := cotangentSumVFormula_37_12_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_12_37_lower, cotangentSumVFormula_12_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_12_lower, cotangentSumVFormula_37_12_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_37_unfold :
    cotangentSumVFormula 13 37 =
      ((13/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 13 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_13_37_lower : ℚ := -1049993229841402552427 / 219902325555200000000
def cotangentSumVFormula_13_37_upper : ℚ := -1049993225443271666323 / 219902325555200000000
theorem cotangentSumVFormula_13_37_bounds :
  ((cotangentSumVFormula_13_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 37 ∧
  cotangentSumVFormula 13 37 ≤ ((cotangentSumVFormula_13_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_37_unfold]
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
  rw [cotangentSumVFormula_13_37_lower, cotangentSumVFormula_13_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_13_unfold :
    cotangentSumVFormula 37 13 =
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
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_37_13_lower : ℚ := 1390755810232338254521 / 439804651110400000000
def cotangentSumVFormula_37_13_upper : ℚ := 1390755819028449245479 / 439804651110400000000
theorem cotangentSumVFormula_37_13_bounds :
  ((cotangentSumVFormula_37_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 13 ∧
  cotangentSumVFormula 37 13 ≤ ((cotangentSumVFormula_37_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_13_unfold]
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
  rw [cotangentSumVFormula_37_13_lower, cotangentSumVFormula_37_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1337_formula_bound :
  (((50320243544882610501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 37) ∧
  (vasyuninBEntryFormula 13 37 ≤ ((50322495344698076999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_13_37_bounds
  have b_Vkh := cotangentSumVFormula_37_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_13_37_lower, cotangentSumVFormula_13_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_13_lower, cotangentSumVFormula_37_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_14_37_unfold :
    cotangentSumVFormula 14 37 =
      ((14/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 14 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_14_37_lower : ℚ := -2087336862701001225333 / 879609302220800000000
def cotangentSumVFormula_14_37_upper : ℚ := -2087336845108453462167 / 879609302220800000000
theorem cotangentSumVFormula_14_37_bounds :
  ((cotangentSumVFormula_14_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 37 ∧
  cotangentSumVFormula 14 37 ≤ ((cotangentSumVFormula_14_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_37_unfold]
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
  rw [cotangentSumVFormula_14_37_lower, cotangentSumVFormula_14_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_14_unfold :
    cotangentSumVFormula 37 14 =
      ((9/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((3/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((1/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_37_14_lower : ℚ := 632637791217057004521 / 439804651110400000000
def cotangentSumVFormula_37_14_upper : ℚ := 1265275600026344975333 / 879609302220800000000
theorem cotangentSumVFormula_37_14_bounds :
  ((cotangentSumVFormula_37_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 14 ∧
  cotangentSumVFormula 37 14 ≤ ((cotangentSumVFormula_37_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_14_unfold]
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
  rw [cotangentSumVFormula_37_14_lower, cotangentSumVFormula_37_14_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1437_formula_bound :
  (((12192528066775304969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 14 37) ∧
  (vasyuninBEntryFormula 14 37 ≤ ((12193091016729163781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 14 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log14 := prim_log_14_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_14_37_bounds
  have b_Vkh := cotangentSumVFormula_37_14_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_14_37_lower, cotangentSumVFormula_14_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_14_lower, cotangentSumVFormula_37_14_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_37_unfold :
    cotangentSumVFormula 15 37 =
      ((15/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 15 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_15_37_lower : ℚ := -2124111881598248881583 / 879609302220800000000
def cotangentSumVFormula_15_37_upper : ℚ := -2124111864005704243417 / 879609302220800000000
theorem cotangentSumVFormula_15_37_bounds :
  ((cotangentSumVFormula_15_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 37 ∧
  cotangentSumVFormula 15 37 ≤ ((cotangentSumVFormula_15_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_37_unfold]
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
  rw [cotangentSumVFormula_15_37_lower, cotangentSumVFormula_15_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_15_unfold :
    cotangentSumVFormula 37 15 =
      ((7/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((4/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_37_15_lower : ℚ := 1734058424179648774667 / 879609302220800000000
def cotangentSumVFormula_37_15_upper : ℚ := 1734058441771886381583 / 879609302220800000000
theorem cotangentSumVFormula_37_15_bounds :
  ((cotangentSumVFormula_37_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 15 ∧
  cotangentSumVFormula 37 15 ≤ ((cotangentSumVFormula_37_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_15_unfold]
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
  rw [cotangentSumVFormula_37_15_lower, cotangentSumVFormula_37_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1537_formula_bound :
  (((95515463499150517877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 37) ∧
  (vasyuninBEntryFormula 15 37 ≤ ((95519967098781169623 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_15_37_bounds
  have b_Vkh := cotangentSumVFormula_37_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_15_37_lower, cotangentSumVFormula_15_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_15_lower, cotangentSumVFormula_37_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_16_37_unfold :
    cotangentSumVFormula 16 37 =
      ((16/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 16 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_16_37_lower : ℚ := 2583754698171194847797 / 14073748835532800000000
def cotangentSumVFormula_16_37_upper : ℚ := 2583754979652055152203 / 14073748835532800000000
theorem cotangentSumVFormula_16_37_bounds :
  ((cotangentSumVFormula_16_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 37 ∧
  cotangentSumVFormula 16 37 ≤ ((cotangentSumVFormula_16_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_37_unfold]
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
  rw [cotangentSumVFormula_16_37_lower, cotangentSumVFormula_16_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_16_unfold :
    cotangentSumVFormula 37 16 =
      ((5/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_37_16_lower : ℚ := -2847212483254487183453 / 14073748835532800000000
def cotangentSumVFormula_37_16_upper : ℚ := -2847212201778675316547 / 14073748835532800000000
theorem cotangentSumVFormula_37_16_bounds :
  ((cotangentSumVFormula_37_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 16 ∧
  cotangentSumVFormula 37 16 ≤ ((cotangentSumVFormula_37_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_16_unfold]
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
  rw [cotangentSumVFormula_37_16_lower, cotangentSumVFormula_37_16_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1637_formula_bound :
  (((93700294783111486627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 16 37) ∧
  (vasyuninBEntryFormula 16 37 ≤ ((93704798382742013373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 16 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log16 := prim_log_16_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_16_37_bounds
  have b_Vkh := cotangentSumVFormula_37_16_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_16_37_lower, cotangentSumVFormula_16_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_16_lower, cotangentSumVFormula_37_16_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_37_unfold :
    cotangentSumVFormula 17 37 =
      ((17/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 17 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_17_37_lower : ℚ := 3474794172440487055917 / 879609302220800000000
def cotangentSumVFormula_17_37_upper : ℚ := 3474794190033050444083 / 879609302220800000000
theorem cotangentSumVFormula_17_37_bounds :
  ((cotangentSumVFormula_17_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 37 ∧
  cotangentSumVFormula 17 37 ≤ ((cotangentSumVFormula_17_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_37_unfold]
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
  rw [cotangentSumVFormula_17_37_lower, cotangentSumVFormula_17_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_17_unfold :
    cotangentSumVFormula 37 17 =
      ((3/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_37_17_lower : ℚ := -1628526273974807839229 / 439804651110400000000
def cotangentSumVFormula_37_17_upper : ℚ := -814263132589338072573 / 219902325555200000000
theorem cotangentSumVFormula_37_17_bounds :
  ((cotangentSumVFormula_37_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 17 ∧
  cotangentSumVFormula 37 17 ≤ ((cotangentSumVFormula_37_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_17_unfold]
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
  rw [cotangentSumVFormula_37_17_lower, cotangentSumVFormula_37_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1737_formula_bound :
  (((11577322027058086219 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 37) ∧
  (vasyuninBEntryFormula 17 37 ≤ ((46311539908047639499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_17_37_bounds
  have b_Vkh := cotangentSumVFormula_37_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_17_37_lower, cotangentSumVFormula_17_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_17_lower, cotangentSumVFormula_37_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_18_37_unfold :
    cotangentSumVFormula 18 37 =
      ((18/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 18 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_18_37_lower : ℚ := 2181902838739115416323 / 219902325555200000000
def cotangentSumVFormula_18_37_upper : ℚ := 2181902843137255677427 / 219902325555200000000
theorem cotangentSumVFormula_18_37_bounds :
  ((cotangentSumVFormula_18_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 37 ∧
  cotangentSumVFormula 18 37 ≤ ((cotangentSumVFormula_18_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_37_unfold]
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
  rw [cotangentSumVFormula_18_37_lower, cotangentSumVFormula_18_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_18_unfold :
    cotangentSumVFormula 37 18 =
      ((1/18 : ℚ) : ℝ) * cotangentTermV 1 18    + 
      ((2/18 : ℚ) : ℝ) * cotangentTermV 2 18    + 
      ((3/18 : ℚ) : ℝ) * cotangentTermV 3 18    + 
      ((4/18 : ℚ) : ℝ) * cotangentTermV 4 18    + 
      ((5/18 : ℚ) : ℝ) * cotangentTermV 5 18    + 
      ((6/18 : ℚ) : ℝ) * cotangentTermV 6 18    + 
      ((7/18 : ℚ) : ℝ) * cotangentTermV 7 18    + 
      ((8/18 : ℚ) : ℝ) * cotangentTermV 8 18    + 
      ((9/18 : ℚ) : ℝ) * cotangentTermV 9 18    + 
      ((10/18 : ℚ) : ℝ) * cotangentTermV 10 18    + 
      ((11/18 : ℚ) : ℝ) * cotangentTermV 11 18    + 
      ((12/18 : ℚ) : ℝ) * cotangentTermV 12 18    + 
      ((13/18 : ℚ) : ℝ) * cotangentTermV 13 18    + 
      ((14/18 : ℚ) : ℝ) * cotangentTermV 14 18    + 
      ((15/18 : ℚ) : ℝ) * cotangentTermV 15 18    + 
      ((16/18 : ℚ) : ℝ) * cotangentTermV 16 18    + 
      ((17/18 : ℚ) : ℝ) * cotangentTermV 17 18 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_18]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_37_18_lower : ℚ := -2124412502007694739927 / 219902325555200000000
def cotangentSumVFormula_37_18_upper : ℚ := -2124412497609621666323 / 219902325555200000000
theorem cotangentSumVFormula_37_18_bounds :
  ((cotangentSumVFormula_37_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 18 ∧
  cotangentSumVFormula 37 18 ≤ ((cotangentSumVFormula_37_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_18_unfold]
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
  rw [cotangentSumVFormula_37_18_lower, cotangentSumVFormula_37_18_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1837_formula_bound :
  (((92681076821991486627 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 18 37) ∧
  (vasyuninBEntryFormula 18 37 ≤ ((92685580421622075873 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 18 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log18 := prim_log_18_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_18_37_bounds
  have b_Vkh := cotangentSumVFormula_37_18_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_18_37_lower, cotangentSumVFormula_18_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_18_lower, cotangentSumVFormula_37_18_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_37_unfold :
    cotangentSumVFormula 19 37 =
      ((19/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 19 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_19_37_lower : ℚ := -1090951421568626080901 / 109951162777600000000
def cotangentSumVFormula_19_37_upper : ℚ := -545475709684779732987 / 54975581388800000000
theorem cotangentSumVFormula_19_37_bounds :
  ((cotangentSumVFormula_19_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 37 ∧
  cotangentSumVFormula 19 37 ≤ ((cotangentSumVFormula_19_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_37_unfold]
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
  rw [cotangentSumVFormula_19_37_lower, cotangentSumVFormula_19_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_19_unfold :
    cotangentSumVFormula 37 19 =
      ((18/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_37_19_lower : ℚ := 577584450150365670487 / 54975581388800000000
def cotangentSumVFormula_37_19_upper : ℚ := 144396112812470594097 / 13743895347200000000
theorem cotangentSumVFormula_37_19_bounds :
  ((cotangentSumVFormula_37_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 19 ∧
  cotangentSumVFormula 37 19 ≤ ((cotangentSumVFormula_37_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_19_unfold]
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
  rw [cotangentSumVFormula_37_19_lower, cotangentSumVFormula_37_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1937_formula_bound :
  (((11363931595035179969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 37) ∧
  (vasyuninBEntryFormula 19 37 ≤ ((11364494544988945031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_19_37_bounds
  have b_Vkh := cotangentSumVFormula_37_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_19_37_lower, cotangentSumVFormula_19_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_19_lower, cotangentSumVFormula_37_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_20_37_unfold :
    cotangentSumVFormula 20 37 =
      ((20/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 20 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_20_37_lower : ℚ := -1737397095016508620479 / 439804651110400000000
def cotangentSumVFormula_20_37_upper : ℚ := -1737397086220251535771 / 439804651110400000000
theorem cotangentSumVFormula_20_37_bounds :
  ((cotangentSumVFormula_20_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 37 ∧
  cotangentSumVFormula 20 37 ≤ ((cotangentSumVFormula_20_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_37_unfold]
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
  rw [cotangentSumVFormula_20_37_lower, cotangentSumVFormula_20_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_20_unfold :
    cotangentSumVFormula 37 20 =
      ((17/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((9/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_37_20_lower : ℚ := 570810380033727044099 / 109951162777600000000
def cotangentSumVFormula_37_20_upper : ℚ := 142702595558190016319 / 27487790694400000000
theorem cotangentSumVFormula_37_20_bounds :
  ((cotangentSumVFormula_37_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 20 ∧
  cotangentSumVFormula 37 20 ≤ ((cotangentSumVFormula_37_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_20_unfold]
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
  rw [cotangentSumVFormula_37_20_lower, cotangentSumVFormula_37_20_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2037_formula_bound :
  (((10935495464735773719 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 20 37) ∧
  (vasyuninBEntryFormula 20 37 ≤ ((10936058414689507531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 20 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log20 := prim_log_20_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_20_37_bounds
  have b_Vkh := cotangentSumVFormula_37_20_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_20_37_lower, cotangentSumVFormula_20_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_20_lower, cotangentSumVFormula_37_20_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_21_37_unfold :
    cotangentSumVFormula 21 37 =
      ((21/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 21 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_21_37_lower : ℚ := -2583754979652109058453 / 14073748835532800000000
def cotangentSumVFormula_21_37_upper : ℚ := -2583754698171240941547 / 14073748835532800000000
theorem cotangentSumVFormula_21_37_bounds :
  ((cotangentSumVFormula_21_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 21 37 ∧
  cotangentSumVFormula 21 37 ≤ ((cotangentSumVFormula_21_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_21_37_unfold]
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
  rw [cotangentSumVFormula_21_37_lower, cotangentSumVFormula_21_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_21_unfold :
    cotangentSumVFormula 37 21 =
      ((16/21 : ℚ) : ℝ) * cotangentTermV 1 21    + 
      ((11/21 : ℚ) : ℝ) * cotangentTermV 2 21    + 
      ((6/21 : ℚ) : ℝ) * cotangentTermV 3 21    + 
      ((1/21 : ℚ) : ℝ) * cotangentTermV 4 21    + 
      ((17/21 : ℚ) : ℝ) * cotangentTermV 5 21    + 
      ((12/21 : ℚ) : ℝ) * cotangentTermV 6 21    + 
      ((7/21 : ℚ) : ℝ) * cotangentTermV 7 21    + 
      ((2/21 : ℚ) : ℝ) * cotangentTermV 8 21    + 
      ((18/21 : ℚ) : ℝ) * cotangentTermV 9 21    + 
      ((13/21 : ℚ) : ℝ) * cotangentTermV 10 21    + 
      ((8/21 : ℚ) : ℝ) * cotangentTermV 11 21    + 
      ((3/21 : ℚ) : ℝ) * cotangentTermV 12 21    + 
      ((19/21 : ℚ) : ℝ) * cotangentTermV 13 21    + 
      ((14/21 : ℚ) : ℝ) * cotangentTermV 14 21    + 
      ((9/21 : ℚ) : ℝ) * cotangentTermV 15 21    + 
      ((4/21 : ℚ) : ℝ) * cotangentTermV 16 21    + 
      ((20/21 : ℚ) : ℝ) * cotangentTermV 17 21    + 
      ((15/21 : ℚ) : ℝ) * cotangentTermV 18 21    + 
      ((10/21 : ℚ) : ℝ) * cotangentTermV 19 21    + 
      ((5/21 : ℚ) : ℝ) * cotangentTermV 20 21 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_21]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((16/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((11/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((6/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((1/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((17/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((12/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((7/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((2/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((18/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((13/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((8/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((3/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((19/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((14/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((9/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((4/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((20/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((15/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((10/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((21 : ℕ) : ℝ)) = ((5/21 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20]
  try ring

def cotangentSumVFormula_37_21_lower : ℚ := 819995993005399973271 / 439804651110400000000
def cotangentSumVFormula_37_21_upper : ℚ := 1639992003603083256583 / 879609302220800000000
theorem cotangentSumVFormula_37_21_bounds :
  ((cotangentSumVFormula_37_21_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 21 ∧
  cotangentSumVFormula 37 21 ≤ ((cotangentSumVFormula_37_21_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_21_unfold]
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
  rw [cotangentSumVFormula_37_21_lower, cotangentSumVFormula_37_21_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2137_formula_bound :
  (((42582691135396141751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 21 37) ∧
  (vasyuninBEntryFormula 21 37 ≤ ((42584942935211170749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 21 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log21 := prim_log_21_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_21_37_bounds
  have b_Vkh := cotangentSumVFormula_37_21_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_21_lower, prim_log_21_upper] at b_log21
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_21_37_lower, cotangentSumVFormula_21_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_21_lower, cotangentSumVFormula_37_21_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_22_37_unfold :
    cotangentSumVFormula 22 37 =
      ((22/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 22 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_22_37_lower : ℚ := 2124111864005699555917 / 879609302220800000000
def cotangentSumVFormula_22_37_upper : ℚ := 2124111881598259819083 / 879609302220800000000
theorem cotangentSumVFormula_22_37_bounds :
  ((cotangentSumVFormula_22_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 22 37 ∧
  cotangentSumVFormula 22 37 ≤ ((cotangentSumVFormula_22_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_22_37_unfold]
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
  rw [cotangentSumVFormula_22_37_lower, cotangentSumVFormula_22_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_22_unfold :
    cotangentSumVFormula 37 22 =
      ((15/22 : ℚ) : ℝ) * cotangentTermV 1 22    + 
      ((8/22 : ℚ) : ℝ) * cotangentTermV 2 22    + 
      ((1/22 : ℚ) : ℝ) * cotangentTermV 3 22    + 
      ((16/22 : ℚ) : ℝ) * cotangentTermV 4 22    + 
      ((9/22 : ℚ) : ℝ) * cotangentTermV 5 22    + 
      ((2/22 : ℚ) : ℝ) * cotangentTermV 6 22    + 
      ((17/22 : ℚ) : ℝ) * cotangentTermV 7 22    + 
      ((10/22 : ℚ) : ℝ) * cotangentTermV 8 22    + 
      ((3/22 : ℚ) : ℝ) * cotangentTermV 9 22    + 
      ((18/22 : ℚ) : ℝ) * cotangentTermV 10 22    + 
      ((11/22 : ℚ) : ℝ) * cotangentTermV 11 22    + 
      ((4/22 : ℚ) : ℝ) * cotangentTermV 12 22    + 
      ((19/22 : ℚ) : ℝ) * cotangentTermV 13 22    + 
      ((12/22 : ℚ) : ℝ) * cotangentTermV 14 22    + 
      ((5/22 : ℚ) : ℝ) * cotangentTermV 15 22    + 
      ((20/22 : ℚ) : ℝ) * cotangentTermV 16 22    + 
      ((13/22 : ℚ) : ℝ) * cotangentTermV 17 22    + 
      ((6/22 : ℚ) : ℝ) * cotangentTermV 18 22    + 
      ((21/22 : ℚ) : ℝ) * cotangentTermV 19 22    + 
      ((14/22 : ℚ) : ℝ) * cotangentTermV 20 22    + 
      ((7/22 : ℚ) : ℝ) * cotangentTermV 21 22 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_22]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((15/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((8/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((1/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((16/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((9/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((2/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((17/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((10/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((3/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((18/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((11/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((4/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((19/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((12/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((5/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((20/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((13/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((6/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((21/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((14/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((22 : ℕ) : ℝ)) = ((7/22 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21]
  try ring

def cotangentSumVFormula_37_22_lower : ℚ := -1459573989049486541957 / 3518437208883200000000
def cotangentSumVFormula_37_22_upper : ℚ := -1459573918680216583043 / 3518437208883200000000
theorem cotangentSumVFormula_37_22_bounds :
  ((cotangentSumVFormula_37_22_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 22 ∧
  cotangentSumVFormula 37 22 ≤ ((cotangentSumVFormula_37_22_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_22_unfold]
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
  rw [cotangentSumVFormula_37_22_lower, cotangentSumVFormula_37_22_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2237_formula_bound :
  (((41699845772033235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 22 37) ∧
  (vasyuninBEntryFormula 22 37 ≤ ((20851048785924155687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 22 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log22 := prim_log_22_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_22_37_bounds
  have b_Vkh := cotangentSumVFormula_37_22_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_22_lower, prim_log_22_upper] at b_log22
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_22_37_lower, cotangentSumVFormula_22_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_22_lower, cotangentSumVFormula_37_22_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_23_37_unfold :
    cotangentSumVFormula 23 37 =
      ((23/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 23 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_23_37_lower : ℚ := 2087336845108451118417 / 879609302220800000000
def cotangentSumVFormula_23_37_upper : ℚ := 2087336862701011381583 / 879609302220800000000
theorem cotangentSumVFormula_23_37_bounds :
  ((cotangentSumVFormula_23_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 23 37 ∧
  cotangentSumVFormula 23 37 ≤ ((cotangentSumVFormula_23_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_23_37_unfold]
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
  rw [cotangentSumVFormula_23_37_lower, cotangentSumVFormula_23_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_23_unfold :
    cotangentSumVFormula 37 23 =
      ((14/23 : ℚ) : ℝ) * cotangentTermV 1 23    + 
      ((5/23 : ℚ) : ℝ) * cotangentTermV 2 23    + 
      ((19/23 : ℚ) : ℝ) * cotangentTermV 3 23    + 
      ((10/23 : ℚ) : ℝ) * cotangentTermV 4 23    + 
      ((1/23 : ℚ) : ℝ) * cotangentTermV 5 23    + 
      ((15/23 : ℚ) : ℝ) * cotangentTermV 6 23    + 
      ((6/23 : ℚ) : ℝ) * cotangentTermV 7 23    + 
      ((20/23 : ℚ) : ℝ) * cotangentTermV 8 23    + 
      ((11/23 : ℚ) : ℝ) * cotangentTermV 9 23    + 
      ((2/23 : ℚ) : ℝ) * cotangentTermV 10 23    + 
      ((16/23 : ℚ) : ℝ) * cotangentTermV 11 23    + 
      ((7/23 : ℚ) : ℝ) * cotangentTermV 12 23    + 
      ((21/23 : ℚ) : ℝ) * cotangentTermV 13 23    + 
      ((12/23 : ℚ) : ℝ) * cotangentTermV 14 23    + 
      ((3/23 : ℚ) : ℝ) * cotangentTermV 15 23    + 
      ((17/23 : ℚ) : ℝ) * cotangentTermV 16 23    + 
      ((8/23 : ℚ) : ℝ) * cotangentTermV 17 23    + 
      ((22/23 : ℚ) : ℝ) * cotangentTermV 18 23    + 
      ((13/23 : ℚ) : ℝ) * cotangentTermV 19 23    + 
      ((4/23 : ℚ) : ℝ) * cotangentTermV 20 23    + 
      ((18/23 : ℚ) : ℝ) * cotangentTermV 21 23    + 
      ((9/23 : ℚ) : ℝ) * cotangentTermV 22 23 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_23]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((14/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((5/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((19/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((10/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((1/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((15/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((6/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((20/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((11/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((2/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((16/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((7/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((21/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((12/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((3/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((17/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((8/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((22/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((13/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((4/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((18/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((23 : ℕ) : ℝ)) = ((9/23 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22]
  try ring

def cotangentSumVFormula_37_23_lower : ℚ := -2862041216203192726281 / 28147497671065600000000
def cotangentSumVFormula_37_23_upper : ℚ := -2862040653248007273719 / 28147497671065600000000
theorem cotangentSumVFormula_37_23_bounds :
  ((cotangentSumVFormula_37_23_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 23 ∧
  cotangentSumVFormula 37 23 ≤ ((cotangentSumVFormula_37_23_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_23_unfold]
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
  rw [cotangentSumVFormula_37_23_lower, cotangentSumVFormula_37_23_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2337_formula_bound :
  (((20456186603291781813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 23 37) ∧
  (vasyuninBEntryFormula 23 37 ≤ ((10228656251599663781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 23 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log23 := log_23_certified_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_23_37_bounds
  have b_Vkh := cotangentSumVFormula_37_23_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_23_lower, log_23_upper] at b_log23
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_23_37_lower, cotangentSumVFormula_23_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_23_lower, cotangentSumVFormula_37_23_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_24_37_unfold :
    cotangentSumVFormula 24 37 =
      ((24/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 24 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_24_37_lower : ℚ := 1049993225443269322573 / 219902325555200000000
def cotangentSumVFormula_24_37_upper : ℚ := 32812288432544086111 / 6871947673600000000
theorem cotangentSumVFormula_24_37_bounds :
  ((cotangentSumVFormula_24_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 24 37 ∧
  cotangentSumVFormula 24 37 ≤ ((cotangentSumVFormula_24_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_24_37_unfold]
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
  rw [cotangentSumVFormula_24_37_lower, cotangentSumVFormula_24_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_24_unfold :
    cotangentSumVFormula 37 24 =
      ((13/24 : ℚ) : ℝ) * cotangentTermV 1 24    + 
      ((2/24 : ℚ) : ℝ) * cotangentTermV 2 24    + 
      ((15/24 : ℚ) : ℝ) * cotangentTermV 3 24    + 
      ((4/24 : ℚ) : ℝ) * cotangentTermV 4 24    + 
      ((17/24 : ℚ) : ℝ) * cotangentTermV 5 24    + 
      ((6/24 : ℚ) : ℝ) * cotangentTermV 6 24    + 
      ((19/24 : ℚ) : ℝ) * cotangentTermV 7 24    + 
      ((8/24 : ℚ) : ℝ) * cotangentTermV 8 24    + 
      ((21/24 : ℚ) : ℝ) * cotangentTermV 9 24    + 
      ((10/24 : ℚ) : ℝ) * cotangentTermV 10 24    + 
      ((23/24 : ℚ) : ℝ) * cotangentTermV 11 24    + 
      ((12/24 : ℚ) : ℝ) * cotangentTermV 12 24    + 
      ((1/24 : ℚ) : ℝ) * cotangentTermV 13 24    + 
      ((14/24 : ℚ) : ℝ) * cotangentTermV 14 24    + 
      ((3/24 : ℚ) : ℝ) * cotangentTermV 15 24    + 
      ((16/24 : ℚ) : ℝ) * cotangentTermV 16 24    + 
      ((5/24 : ℚ) : ℝ) * cotangentTermV 17 24    + 
      ((18/24 : ℚ) : ℝ) * cotangentTermV 18 24    + 
      ((7/24 : ℚ) : ℝ) * cotangentTermV 19 24    + 
      ((20/24 : ℚ) : ℝ) * cotangentTermV 20 24    + 
      ((9/24 : ℚ) : ℝ) * cotangentTermV 21 24    + 
      ((22/24 : ℚ) : ℝ) * cotangentTermV 22 24    + 
      ((11/24 : ℚ) : ℝ) * cotangentTermV 23 24 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_24]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((13/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((2/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((15/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((4/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((17/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((6/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((19/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((8/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((21/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((10/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((23/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((12/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((1/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((14/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((3/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((16/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((5/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((18/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((7/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((20/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((9/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((22/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((24 : ℕ) : ℝ)) = ((11/24 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23]
  try ring

def cotangentSumVFormula_37_24_lower : ℚ := -2061240081869835600333 / 879609302220800000000
def cotangentSumVFormula_37_24_upper : ℚ := -2061240064277474555917 / 879609302220800000000
theorem cotangentSumVFormula_37_24_bounds :
  ((cotangentSumVFormula_37_24_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 24 ∧
  cotangentSumVFormula 37 24 ≤ ((cotangentSumVFormula_37_24_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_24_unfold]
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
  rw [cotangentSumVFormula_37_24_lower, cotangentSumVFormula_37_24_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2437_formula_bound :
  (((40340110362767891751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 24 37) ∧
  (vasyuninBEntryFormula 24 37 ≤ ((5042795270322870953 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 24 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log24 := prim_log_24_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_24_37_bounds
  have b_Vkh := cotangentSumVFormula_37_24_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_24_lower, prim_log_24_upper] at b_log24
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_24_37_lower, cotangentSumVFormula_24_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_24_lower, cotangentSumVFormula_37_24_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_25_37_unfold :
    cotangentSumVFormula 25 37 =
      ((25/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((26/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 25 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_25_37_lower : ℚ := -2333917624894008256583 / 879609302220800000000
def cotangentSumVFormula_25_37_upper : ℚ := -2333917607301483149667 / 879609302220800000000
theorem cotangentSumVFormula_25_37_bounds :
  ((cotangentSumVFormula_25_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 25 37 ∧
  cotangentSumVFormula 25 37 ≤ ((cotangentSumVFormula_25_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_25_37_unfold]
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
  rw [cotangentSumVFormula_25_37_lower, cotangentSumVFormula_25_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_25_unfold :
    cotangentSumVFormula 37 25 =
      ((12/25 : ℚ) : ℝ) * cotangentTermV 1 25    + 
      ((24/25 : ℚ) : ℝ) * cotangentTermV 2 25    + 
      ((11/25 : ℚ) : ℝ) * cotangentTermV 3 25    + 
      ((23/25 : ℚ) : ℝ) * cotangentTermV 4 25    + 
      ((10/25 : ℚ) : ℝ) * cotangentTermV 5 25    + 
      ((22/25 : ℚ) : ℝ) * cotangentTermV 6 25    + 
      ((9/25 : ℚ) : ℝ) * cotangentTermV 7 25    + 
      ((21/25 : ℚ) : ℝ) * cotangentTermV 8 25    + 
      ((8/25 : ℚ) : ℝ) * cotangentTermV 9 25    + 
      ((20/25 : ℚ) : ℝ) * cotangentTermV 10 25    + 
      ((7/25 : ℚ) : ℝ) * cotangentTermV 11 25    + 
      ((19/25 : ℚ) : ℝ) * cotangentTermV 12 25    + 
      ((6/25 : ℚ) : ℝ) * cotangentTermV 13 25    + 
      ((18/25 : ℚ) : ℝ) * cotangentTermV 14 25    + 
      ((5/25 : ℚ) : ℝ) * cotangentTermV 15 25    + 
      ((17/25 : ℚ) : ℝ) * cotangentTermV 16 25    + 
      ((4/25 : ℚ) : ℝ) * cotangentTermV 17 25    + 
      ((16/25 : ℚ) : ℝ) * cotangentTermV 18 25    + 
      ((3/25 : ℚ) : ℝ) * cotangentTermV 19 25    + 
      ((15/25 : ℚ) : ℝ) * cotangentTermV 20 25    + 
      ((2/25 : ℚ) : ℝ) * cotangentTermV 21 25    + 
      ((14/25 : ℚ) : ℝ) * cotangentTermV 22 25    + 
      ((1/25 : ℚ) : ℝ) * cotangentTermV 23 25    + 
      ((13/25 : ℚ) : ℝ) * cotangentTermV 24 25 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_25]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((12/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((24/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((11/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((23/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((10/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((22/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((9/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((21/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((8/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((20/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((7/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((19/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((6/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((18/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((5/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((17/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((4/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((16/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((3/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((15/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((2/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((14/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((1/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((25 : ℕ) : ℝ)) = ((13/25 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24]
  try ring

def cotangentSumVFormula_37_25_lower : ℚ := 1143420832327873228823 / 219902325555200000000
def cotangentSumVFormula_37_25_upper : ℚ := 571710418362979205901 / 109951162777600000000
theorem cotangentSumVFormula_37_25_bounds :
  ((cotangentSumVFormula_37_25_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 25 ∧
  cotangentSumVFormula 37 25 ≤ ((cotangentSumVFormula_37_25_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_25_unfold]
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
  rw [cotangentSumVFormula_37_25_lower, cotangentSumVFormula_37_25_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2537_formula_bound :
  (((39835650429907766751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 25 37) ∧
  (vasyuninBEntryFormula 25 37 ≤ ((9959475557430663781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 25 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log25 := prim_log_25_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_25_37_bounds
  have b_Vkh := cotangentSumVFormula_37_25_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_25_lower, prim_log_25_upper] at b_log25
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_25_37_lower, cotangentSumVFormula_25_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_25_lower, cotangentSumVFormula_37_25_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_26_37_unfold :
    cotangentSumVFormula 26 37 =
      ((26/37 : ℚ) : ℝ) * cotangentTermV 1 37    + 
      ((15/37 : ℚ) : ℝ) * cotangentTermV 2 37    + 
      ((4/37 : ℚ) : ℝ) * cotangentTermV 3 37    + 
      ((30/37 : ℚ) : ℝ) * cotangentTermV 4 37    + 
      ((19/37 : ℚ) : ℝ) * cotangentTermV 5 37    + 
      ((8/37 : ℚ) : ℝ) * cotangentTermV 6 37    + 
      ((34/37 : ℚ) : ℝ) * cotangentTermV 7 37    + 
      ((23/37 : ℚ) : ℝ) * cotangentTermV 8 37    + 
      ((12/37 : ℚ) : ℝ) * cotangentTermV 9 37    + 
      ((1/37 : ℚ) : ℝ) * cotangentTermV 10 37    + 
      ((27/37 : ℚ) : ℝ) * cotangentTermV 11 37    + 
      ((16/37 : ℚ) : ℝ) * cotangentTermV 12 37    + 
      ((5/37 : ℚ) : ℝ) * cotangentTermV 13 37    + 
      ((31/37 : ℚ) : ℝ) * cotangentTermV 14 37    + 
      ((20/37 : ℚ) : ℝ) * cotangentTermV 15 37    + 
      ((9/37 : ℚ) : ℝ) * cotangentTermV 16 37    + 
      ((35/37 : ℚ) : ℝ) * cotangentTermV 17 37    + 
      ((24/37 : ℚ) : ℝ) * cotangentTermV 18 37    + 
      ((13/37 : ℚ) : ℝ) * cotangentTermV 19 37    + 
      ((2/37 : ℚ) : ℝ) * cotangentTermV 20 37    + 
      ((28/37 : ℚ) : ℝ) * cotangentTermV 21 37    + 
      ((17/37 : ℚ) : ℝ) * cotangentTermV 22 37    + 
      ((6/37 : ℚ) : ℝ) * cotangentTermV 23 37    + 
      ((32/37 : ℚ) : ℝ) * cotangentTermV 24 37    + 
      ((21/37 : ℚ) : ℝ) * cotangentTermV 25 37    + 
      ((10/37 : ℚ) : ℝ) * cotangentTermV 26 37    + 
      ((36/37 : ℚ) : ℝ) * cotangentTermV 27 37    + 
      ((25/37 : ℚ) : ℝ) * cotangentTermV 28 37    + 
      ((14/37 : ℚ) : ℝ) * cotangentTermV 29 37    + 
      ((3/37 : ℚ) : ℝ) * cotangentTermV 30 37    + 
      ((29/37 : ℚ) : ℝ) * cotangentTermV 31 37    + 
      ((18/37 : ℚ) : ℝ) * cotangentTermV 32 37    + 
      ((7/37 : ℚ) : ℝ) * cotangentTermV 33 37    + 
      ((33/37 : ℚ) : ℝ) * cotangentTermV 34 37    + 
      ((22/37 : ℚ) : ℝ) * cotangentTermV 35 37    + 
      ((11/37 : ℚ) : ℝ) * cotangentTermV 36 37 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_37]
  have hf_1 : Int.fract (((1 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((26/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((15/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((4/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((30/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((19/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((8/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((34/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((23/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((12/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((1/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((27/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((16/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((5/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((31/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((20/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((9/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((35/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((24/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((13/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((2/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((28/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((17/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((6/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((32/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((21/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_26 : Int.fract (((26 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((10/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_27 : Int.fract (((27 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((36/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_28 : Int.fract (((28 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((25/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_29 : Int.fract (((29 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((14/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_30 : Int.fract (((30 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((3/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_31 : Int.fract (((31 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((29/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_32 : Int.fract (((32 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((18/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_33 : Int.fract (((33 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((7/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_34 : Int.fract (((34 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((33/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_35 : Int.fract (((35 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((22/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_36 : Int.fract (((36 * 26 : ℕ) : ℝ) / ((37 : ℕ) : ℝ)) = ((11/37 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25, hf_26, hf_27, hf_28, hf_29, hf_30, hf_31, hf_32, hf_33, hf_34, hf_35, hf_36]
  try ring

def cotangentSumVFormula_26_37_lower : ℚ := 3510966473552135439959 / 1759218604441600000000
def cotangentSumVFormula_26_37_upper : ℚ := 3510966508737230185041 / 1759218604441600000000
theorem cotangentSumVFormula_26_37_bounds :
  ((cotangentSumVFormula_26_37_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 26 37 ∧
  cotangentSumVFormula 26 37 ≤ ((cotangentSumVFormula_26_37_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_26_37_unfold]
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
  rw [cotangentSumVFormula_26_37_lower, cotangentSumVFormula_26_37_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_37_26_unfold :
    cotangentSumVFormula 37 26 =
      ((11/26 : ℚ) : ℝ) * cotangentTermV 1 26    + 
      ((22/26 : ℚ) : ℝ) * cotangentTermV 2 26    + 
      ((7/26 : ℚ) : ℝ) * cotangentTermV 3 26    + 
      ((18/26 : ℚ) : ℝ) * cotangentTermV 4 26    + 
      ((3/26 : ℚ) : ℝ) * cotangentTermV 5 26    + 
      ((14/26 : ℚ) : ℝ) * cotangentTermV 6 26    + 
      ((25/26 : ℚ) : ℝ) * cotangentTermV 7 26    + 
      ((10/26 : ℚ) : ℝ) * cotangentTermV 8 26    + 
      ((21/26 : ℚ) : ℝ) * cotangentTermV 9 26    + 
      ((6/26 : ℚ) : ℝ) * cotangentTermV 10 26    + 
      ((17/26 : ℚ) : ℝ) * cotangentTermV 11 26    + 
      ((2/26 : ℚ) : ℝ) * cotangentTermV 12 26    + 
      ((13/26 : ℚ) : ℝ) * cotangentTermV 13 26    + 
      ((24/26 : ℚ) : ℝ) * cotangentTermV 14 26    + 
      ((9/26 : ℚ) : ℝ) * cotangentTermV 15 26    + 
      ((20/26 : ℚ) : ℝ) * cotangentTermV 16 26    + 
      ((5/26 : ℚ) : ℝ) * cotangentTermV 17 26    + 
      ((16/26 : ℚ) : ℝ) * cotangentTermV 18 26    + 
      ((1/26 : ℚ) : ℝ) * cotangentTermV 19 26    + 
      ((12/26 : ℚ) : ℝ) * cotangentTermV 20 26    + 
      ((23/26 : ℚ) : ℝ) * cotangentTermV 21 26    + 
      ((8/26 : ℚ) : ℝ) * cotangentTermV 22 26    + 
      ((19/26 : ℚ) : ℝ) * cotangentTermV 23 26    + 
      ((4/26 : ℚ) : ℝ) * cotangentTermV 24 26    + 
      ((15/26 : ℚ) : ℝ) * cotangentTermV 25 26 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_26]
  have hf_1 : Int.fract (((1 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((11/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((22/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((7/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((18/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((3/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((14/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((25/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((10/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((21/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((6/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((17/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((2/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((13/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((24/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((9/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((20/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((5/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((16/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((1/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_20 : Int.fract (((20 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((12/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_21 : Int.fract (((21 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((23/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_22 : Int.fract (((22 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((8/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_23 : Int.fract (((23 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((19/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_24 : Int.fract (((24 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((4/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_25 : Int.fract (((25 * 37 : ℕ) : ℝ) / ((26 : ℕ) : ℝ)) = ((15/26 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19, hf_20, hf_21, hf_22, hf_23, hf_24, hf_25]
  try ring

def cotangentSumVFormula_37_26_lower : ℚ := 686419269468702680917 / 879609302220800000000
def cotangentSumVFormula_37_26_upper : ℚ := 686419287061089506583 / 879609302220800000000
theorem cotangentSumVFormula_37_26_bounds :
  ((cotangentSumVFormula_37_26_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 37 26 ∧
  cotangentSumVFormula 37 26 ≤ ((cotangentSumVFormula_37_26_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_37_26_unfold]
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
  rw [cotangentSumVFormula_37_26_lower, cotangentSumVFormula_37_26_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_2637_formula_bound :
  (((39100599243347391751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 26 37) ∧
  (vasyuninBEntryFormula 26 37 ≤ ((39102851043162389499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 26 37 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log26 := prim_log_26_bounds
  have b_log37 := log_37_certified_bounds
  have b_Vhk := cotangentSumVFormula_26_37_bounds
  have b_Vkh := cotangentSumVFormula_37_26_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_26_lower, prim_log_26_upper] at b_log26
  simp only [log_37_lower, log_37_upper] at b_log37
  simp only [cotangentSumVFormula_26_37_lower, cotangentSumVFormula_26_37_upper] at b_Vhk
  simp only [cotangentSumVFormula_37_26_lower, cotangentSumVFormula_37_26_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
