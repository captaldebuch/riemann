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

theorem cotangentSumVFormula_1_11_unfold :
    cotangentSumVFormula 1 11 =
      ((1/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_1_11_lower : ℚ := -947374301334035364927 / 219902325555200000000
def cotangentSumVFormula_1_11_upper : ℚ := -947374296935981041323 / 219902325555200000000
theorem cotangentSumVFormula_1_11_bounds :
  ((cotangentSumVFormula_1_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 11 ∧
  cotangentSumVFormula 1 11 ≤ ((cotangentSumVFormula_1_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_11_unfold]
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
  rw [cotangentSumVFormula_1_11_lower, cotangentSumVFormula_1_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_1_unfold :
    cotangentSumVFormula 11 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_11_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_11_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_11_1_bounds :
  ((cotangentSumVFormula_11_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 1 ∧
  cotangentSumVFormula 11 1 ≤ ((cotangentSumVFormula_11_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_1_unfold]
  rw [cotangentSumVFormula_11_1_lower, cotangentSumVFormula_11_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_111_formula_bound :
  (((14980368267640181711 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 11) ∧
  (vasyuninBEntryFormula 1 11 ≤ ((14980509005129099539 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_11_bounds
  have b_Vkh := cotangentSumVFormula_11_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_1_11_lower, cotangentSumVFormula_1_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_1_lower, cotangentSumVFormula_11_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_11_unfold :
    cotangentSumVFormula 2 11 =
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
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_2_11_lower : ℚ := -1924262803088862162833 / 879609302220800000000
def cotangentSumVFormula_2_11_upper : ℚ := -1924262785496647212167 / 879609302220800000000
theorem cotangentSumVFormula_2_11_bounds :
  ((cotangentSumVFormula_2_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 11 ∧
  cotangentSumVFormula 2 11 ≤ ((cotangentSumVFormula_2_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_11_unfold]
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
  rw [cotangentSumVFormula_2_11_lower, cotangentSumVFormula_2_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_2_unfold :
    cotangentSumVFormula 11 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_11_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_11_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_11_2_bounds :
  ((cotangentSumVFormula_11_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 2 ∧
  cotangentSumVFormula 11 2 ≤ ((cotangentSumVFormula_11_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_11_2_lower, cotangentSumVFormula_11_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_211_formula_bound :
  (((101311477538224844313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 11) ∧
  (vasyuninBEntryFormula 2 11 ≤ ((101312603438133686937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_11_bounds
  have b_Vkh := cotangentSumVFormula_11_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_2_11_lower, cotangentSumVFormula_2_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_2_lower, cotangentSumVFormula_11_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_11_unfold :
    cotangentSumVFormula 3 11 =
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
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_3_11_lower : ℚ := -2230748134936280966291 / 1759218604441600000000
def cotangentSumVFormula_3_11_upper : ℚ := -2230748099751851064959 / 1759218604441600000000
theorem cotangentSumVFormula_3_11_bounds :
  ((cotangentSumVFormula_3_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 11 ∧
  cotangentSumVFormula 3 11 ≤ ((cotangentSumVFormula_3_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_11_unfold]
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
  rw [cotangentSumVFormula_3_11_lower, cotangentSumVFormula_3_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_3_unfold :
    cotangentSumVFormula 11 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_11_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_11_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_11_3_bounds :
  ((cotangentSumVFormula_11_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 3 ∧
  cotangentSumVFormula 11 3 ≤ ((cotangentSumVFormula_11_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_11_3_lower, cotangentSumVFormula_11_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_311_formula_bound :
  (((90702962854524219313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 11) ∧
  (vasyuninBEntryFormula 3 11 ≤ ((90704088754432436937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_11_bounds
  have b_Vkh := cotangentSumVFormula_11_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_3_11_lower, cotangentSumVFormula_3_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_3_lower, cotangentSumVFormula_11_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_11_unfold :
    cotangentSumVFormula 4 11 =
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
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_4_11_lower : ℚ := -3098045053564121698207 / 3518437208883200000000
def cotangentSumVFormula_4_11_upper : ℚ := -3098044983195265801793 / 3518437208883200000000
theorem cotangentSumVFormula_4_11_bounds :
  ((cotangentSumVFormula_4_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 11 ∧
  cotangentSumVFormula 4 11 ≤ ((cotangentSumVFormula_4_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_11_unfold]
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
  rw [cotangentSumVFormula_4_11_lower, cotangentSumVFormula_4_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_4_unfold :
    cotangentSumVFormula 11 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_11_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_11_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_11_4_bounds :
  ((cotangentSumVFormula_11_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 4 ∧
  cotangentSumVFormula 11 4 ≤ ((cotangentSumVFormula_11_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_11_4_lower, cotangentSumVFormula_11_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_411_formula_bound :
  (((41658479390614586219 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 11) ∧
  (vasyuninBEntryFormula 4 11 ≤ ((41659042340568507531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_11_bounds
  have b_Vkh := cotangentSumVFormula_11_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_4_11_lower, cotangentSumVFormula_4_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_4_lower, cotangentSumVFormula_11_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_11_unfold :
    cotangentSumVFormula 5 11 =
      ((5/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_5_11_lower : ℚ := 1675571378290838564959 / 1759218604441600000000
def cotangentSumVFormula_5_11_upper : ℚ := 1675571413475262216291 / 1759218604441600000000
theorem cotangentSumVFormula_5_11_bounds :
  ((cotangentSumVFormula_5_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 11 ∧
  cotangentSumVFormula 5 11 ≤ ((cotangentSumVFormula_5_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_11_unfold]
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
  rw [cotangentSumVFormula_5_11_lower, cotangentSumVFormula_5_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_5_unfold :
    cotangentSumVFormula 11 5 =
      ((1/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_11_5_lower : ℚ := -3134269962581291229457 / 3518437208883200000000
def cotangentSumVFormula_11_5_upper : ℚ := -3134269892212532208043 / 3518437208883200000000
theorem cotangentSumVFormula_11_5_bounds :
  ((cotangentSumVFormula_11_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 5 ∧
  cotangentSumVFormula 11 5 ≤ ((cotangentSumVFormula_11_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_11_5_lower, cotangentSumVFormula_11_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_511_formula_bound :
  (((19506322987050004047 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 11) ∧
  (vasyuninBEntryFormula 5 11 ≤ ((4876651115506729457 / 35184372088832000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_11_bounds
  have b_Vkh := cotangentSumVFormula_11_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_5_11_lower, cotangentSumVFormula_5_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_5_lower, cotangentSumVFormula_11_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_11_unfold :
    cotangentSumVFormula 6 11 =
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
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 6 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_6_11_lower : ℚ := -3351142826950507635707 / 3518437208883200000000
def cotangentSumVFormula_6_11_upper : ℚ := -3351142756581654864293 / 3518437208883200000000
theorem cotangentSumVFormula_6_11_bounds :
  ((cotangentSumVFormula_6_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 11 ∧
  cotangentSumVFormula 6 11 ≤ ((cotangentSumVFormula_6_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_11_unfold]
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
  rw [cotangentSumVFormula_6_11_lower, cotangentSumVFormula_6_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_6_unfold :
    cotangentSumVFormula 11 6 =
      ((5/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((1/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_11_6_lower : ℚ := 148120776897660637849 / 109951162777600000000
def cotangentSumVFormula_11_6_upper : ℚ := 1184966232773477787833 / 879609302220800000000
theorem cotangentSumVFormula_11_6_bounds :
  ((cotangentSumVFormula_11_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 6 ∧
  cotangentSumVFormula 11 6 ≤ ((cotangentSumVFormula_11_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_6_unfold]
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
  rw [cotangentSumVFormula_11_6_lower, cotangentSumVFormula_11_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_611_formula_bound :
  (((73185416109330313063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 11) ∧
  (vasyuninBEntryFormula 6 11 ≤ ((73186542009237936937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_11_bounds
  have b_Vkh := cotangentSumVFormula_11_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_6_11_lower, cotangentSumVFormula_6_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_6_lower, cotangentSumVFormula_11_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_11_unfold :
    cotangentSumVFormula 7 11 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_7_11_lower : ℚ := 774511245798822212167 / 879609302220800000000
def cotangentSumVFormula_7_11_upper : ℚ := 774511263391034037833 / 879609302220800000000
theorem cotangentSumVFormula_7_11_bounds :
  ((cotangentSumVFormula_7_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 11 ∧
  cotangentSumVFormula 7 11 ≤ ((cotangentSumVFormula_7_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_11_unfold]
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
  rw [cotangentSumVFormula_7_11_lower, cotangentSumVFormula_7_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_7_unfold :
    cotangentSumVFormula 11 7 =
      ((4/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_11_7_lower : ℚ := -2465148184743653589703 / 14073748835532800000000
def cotangentSumVFormula_11_7_upper : ℚ := -2465147903268565160297 / 14073748835532800000000
theorem cotangentSumVFormula_11_7_bounds :
  ((cotangentSumVFormula_11_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 7 ∧
  cotangentSumVFormula 11 7 ≤ ((cotangentSumVFormula_11_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_7_unfold]
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
  rw [cotangentSumVFormula_11_7_lower, cotangentSumVFormula_11_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_711_formula_bound :
  (((4265045715543395543 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 11) ∧
  (vasyuninBEntryFormula 7 11 ≤ ((68241857348601811937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_7_11_bounds
  have b_Vkh := cotangentSumVFormula_11_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_7_11_lower, cotangentSumVFormula_7_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_7_lower, cotangentSumVFormula_11_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_11_unfold :
    cotangentSumVFormula 8 11 =
      ((8/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_8_11_lower : ℚ := 1115374049875932368417 / 879609302220800000000
def cotangentSumVFormula_8_11_upper : ℚ := 1115374067468143412833 / 879609302220800000000
theorem cotangentSumVFormula_8_11_bounds :
  ((cotangentSumVFormula_8_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 11 ∧
  cotangentSumVFormula 8 11 ≤ ((cotangentSumVFormula_8_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_11_unfold]
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
  rw [cotangentSumVFormula_8_11_lower, cotangentSumVFormula_8_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_8_unfold :
    cotangentSumVFormula 11 8 =
      ((3/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_11_8_lower : ℚ := -728692222730972372541 / 1759218604441600000000
def cotangentSumVFormula_11_8_upper : ℚ := -728692187546586221209 / 1759218604441600000000
theorem cotangentSumVFormula_11_8_bounds :
  ((cotangentSumVFormula_11_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 8 ∧
  cotangentSumVFormula 11 8 ≤ ((cotangentSumVFormula_11_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_8_unfold]
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
  rw [cotangentSumVFormula_11_8_lower, cotangentSumVFormula_11_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_811_formula_bound :
  (((129956197128701141751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 11) ∧
  (vasyuninBEntryFormula 8 11 ≤ ((129958448928515920749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_8_11_bounds
  have b_Vkh := cotangentSumVFormula_11_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_8_11_lower, cotangentSumVFormula_8_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_8_lower, cotangentSumVFormula_11_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_11_unfold :
    cotangentSumVFormula 9 11 =
      ((9/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_9_11_lower : ℚ := 962131392748326535771 / 439804651110400000000
def cotangentSumVFormula_9_11_upper : ℚ := 962131401544432839229 / 439804651110400000000
theorem cotangentSumVFormula_9_11_bounds :
  ((cotangentSumVFormula_9_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 11 ∧
  cotangentSumVFormula 9 11 ≤ ((cotangentSumVFormula_9_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_11_unfold]
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
  rw [cotangentSumVFormula_9_11_lower, cotangentSumVFormula_9_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_9_unfold :
    cotangentSumVFormula 11 9 =
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
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_11_9_lower : ℚ := -1169176792736990287833 / 879609302220800000000
def cotangentSumVFormula_11_9_upper : ℚ := -1169176775144784712167 / 879609302220800000000
theorem cotangentSumVFormula_11_9_bounds :
  ((cotangentSumVFormula_11_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 9 ∧
  cotangentSumVFormula 11 9 ≤ ((cotangentSumVFormula_11_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_9_unfold]
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
  rw [cotangentSumVFormula_11_9_lower, cotangentSumVFormula_11_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_911_formula_bound :
  (((125753014742138735501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 11) ∧
  (vasyuninBEntryFormula 9 11 ≤ ((125755266541953701999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_9_11_bounds
  have b_Vkh := cotangentSumVFormula_11_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_9_11_lower, cotangentSumVFormula_9_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_9_lower, cotangentSumVFormula_11_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_11_unfold :
    cotangentSumVFormula 10 11 =
      ((10/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_10_11_lower : ℚ := 947374296935982603823 / 219902325555200000000
def cotangentSumVFormula_10_11_upper : ℚ := 947374301334036146177 / 219902325555200000000
theorem cotangentSumVFormula_10_11_bounds :
  ((cotangentSumVFormula_10_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 11 ∧
  cotangentSumVFormula 10 11 ≤ ((cotangentSumVFormula_10_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_11_unfold]
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
  rw [cotangentSumVFormula_10_11_lower, cotangentSumVFormula_10_11_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_11_10_unfold :
    cotangentSumVFormula 11 10 =
      ((1/10 : ℚ) : ℝ) * cotangentTermV 1 10    + 
      ((2/10 : ℚ) : ℝ) * cotangentTermV 2 10    + 
      ((3/10 : ℚ) : ℝ) * cotangentTermV 3 10    + 
      ((4/10 : ℚ) : ℝ) * cotangentTermV 4 10    + 
      ((5/10 : ℚ) : ℝ) * cotangentTermV 5 10    + 
      ((6/10 : ℚ) : ℝ) * cotangentTermV 6 10    + 
      ((7/10 : ℚ) : ℝ) * cotangentTermV 7 10    + 
      ((8/10 : ℚ) : ℝ) * cotangentTermV 8 10    + 
      ((9/10 : ℚ) : ℝ) * cotangentTermV 9 10 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_10]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_11_10_lower : ℚ := -1602462085977636745479 / 439804651110400000000
def cotangentSumVFormula_11_10_upper : ℚ := -801231038590768541323 / 219902325555200000000
theorem cotangentSumVFormula_11_10_bounds :
  ((cotangentSumVFormula_11_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 10 ∧
  cotangentSumVFormula 11 10 ≤ ((cotangentSumVFormula_11_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_10_unfold]
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
  rw [cotangentSumVFormula_11_10_lower, cotangentSumVFormula_11_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1011_formula_bound :
  (((31078050659057179969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 11) ∧
  (vasyuninBEntryFormula 10 11 ≤ ((31078613609010851281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 11 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log11 := log_11_certified_bounds
  have b_Vhk := cotangentSumVFormula_10_11_bounds
  have b_Vkh := cotangentSumVFormula_11_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [cotangentSumVFormula_10_11_lower, cotangentSumVFormula_10_11_upper] at b_Vhk
  simp only [cotangentSumVFormula_11_10_lower, cotangentSumVFormula_11_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_12_unfold :
    cotangentSumVFormula 1 12 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_1_12_lower : ℚ := -34372459555962836111 / 6871947673600000000
def cotangentSumVFormula_1_12_upper : ℚ := -1099918701392752135073 / 219902325555200000000
theorem cotangentSumVFormula_1_12_bounds :
  ((cotangentSumVFormula_1_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 12 ∧
  cotangentSumVFormula 1 12 ≤ ((cotangentSumVFormula_1_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_12_unfold]
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
  rw [cotangentSumVFormula_1_12_lower, cotangentSumVFormula_1_12_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_12_1_unfold :
    cotangentSumVFormula 12 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_12_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_12_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_12_1_bounds :
  ((cotangentSumVFormula_12_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 1 ∧
  cotangentSumVFormula 12 1 ≤ ((cotangentSumVFormula_12_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_1_unfold]
  rw [cotangentSumVFormula_12_1_lower, cotangentSumVFormula_12_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_112_formula_bound :
  (((111848302969463250563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 12) ∧
  (vasyuninBEntryFormula 1 12 ≤ ((111849428869375874437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 12 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log12 := prim_log_12_bounds
  have b_Vhk := cotangentSumVFormula_1_12_bounds
  have b_Vkh := cotangentSumVFormula_12_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [cotangentSumVFormula_1_12_lower, cotangentSumVFormula_1_12_upper] at b_Vhk
  simp only [cotangentSumVFormula_12_1_lower, cotangentSumVFormula_12_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_12_unfold :
    cotangentSumVFormula 5 12 =
      ((5/12 : ℚ) : ℝ) * cotangentTermV 1 12    + 
      ((10/12 : ℚ) : ℝ) * cotangentTermV 2 12    + 
      ((3/12 : ℚ) : ℝ) * cotangentTermV 3 12    + 
      ((8/12 : ℚ) : ℝ) * cotangentTermV 4 12    + 
      ((1/12 : ℚ) : ℝ) * cotangentTermV 5 12    + 
      ((6/12 : ℚ) : ℝ) * cotangentTermV 6 12    + 
      ((11/12 : ℚ) : ℝ) * cotangentTermV 7 12    + 
      ((4/12 : ℚ) : ℝ) * cotangentTermV 8 12    + 
      ((9/12 : ℚ) : ℝ) * cotangentTermV 9 12    + 
      ((2/12 : ℚ) : ℝ) * cotangentTermV 10 12    + 
      ((7/12 : ℚ) : ℝ) * cotangentTermV 11 12 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_12]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_5_12_lower : ℚ := 833686767119254270129 / 450359962737049600000000
def cotangentSumVFormula_5_12_upper : ℚ := 833695774338345729871 / 450359962737049600000000
theorem cotangentSumVFormula_5_12_bounds :
  ((cotangentSumVFormula_5_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 12 ∧
  cotangentSumVFormula 5 12 ≤ ((cotangentSumVFormula_5_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_12_unfold]
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
  rw [cotangentSumVFormula_5_12_lower, cotangentSumVFormula_5_12_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_12_5_unfold :
    cotangentSumVFormula 12 5 =
      ((2/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_12_5_lower : ℚ := -2260935825867423195031 / 28147497671065600000000
def cotangentSumVFormula_12_5_upper : ℚ := -2260935262917351804969 / 28147497671065600000000
theorem cotangentSumVFormula_12_5_bounds :
  ((cotangentSumVFormula_12_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 5 ∧
  cotangentSumVFormula 12 5 ≤ ((cotangentSumVFormula_12_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_12_5_lower, cotangentSumVFormula_12_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_512_formula_bound :
  (((72945995308047125563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 12) ∧
  (vasyuninBEntryFormula 5 12 ≤ ((72947121207954968187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 12 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log12 := prim_log_12_bounds
  have b_Vhk := cotangentSumVFormula_5_12_bounds
  have b_Vkh := cotangentSumVFormula_12_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [cotangentSumVFormula_5_12_lower, cotangentSumVFormula_5_12_upper] at b_Vhk
  simp only [cotangentSumVFormula_12_5_lower, cotangentSumVFormula_12_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_12_unfold :
    cotangentSumVFormula 7 12 =
      ((7/12 : ℚ) : ℝ) * cotangentTermV 1 12    + 
      ((2/12 : ℚ) : ℝ) * cotangentTermV 2 12    + 
      ((9/12 : ℚ) : ℝ) * cotangentTermV 3 12    + 
      ((4/12 : ℚ) : ℝ) * cotangentTermV 4 12    + 
      ((11/12 : ℚ) : ℝ) * cotangentTermV 5 12    + 
      ((6/12 : ℚ) : ℝ) * cotangentTermV 6 12    + 
      ((1/12 : ℚ) : ℝ) * cotangentTermV 7 12    + 
      ((8/12 : ℚ) : ℝ) * cotangentTermV 8 12    + 
      ((3/12 : ℚ) : ℝ) * cotangentTermV 9 12    + 
      ((10/12 : ℚ) : ℝ) * cotangentTermV 10 12    + 
      ((5/12 : ℚ) : ℝ) * cotangentTermV 11 12 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_12]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_7_12_lower : ℚ := -3334783097327908310109 / 1801439850948198400000000
def cotangentSumVFormula_7_12_upper : ℚ := -3334747068459291689891 / 1801439850948198400000000
theorem cotangentSumVFormula_7_12_bounds :
  ((cotangentSumVFormula_7_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 12 ∧
  cotangentSumVFormula 7 12 ≤ ((cotangentSumVFormula_7_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_12_unfold]
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
  rw [cotangentSumVFormula_7_12_lower, cotangentSumVFormula_7_12_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_12_7_unfold :
    cotangentSumVFormula 12 7 =
      ((5/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_12_7_lower : ℚ := 2156738354928926739293 / 3518437208883200000000
def cotangentSumVFormula_12_7_upper : ℚ := 2156738425297699041957 / 3518437208883200000000
theorem cotangentSumVFormula_12_7_bounds :
  ((cotangentSumVFormula_12_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 7 ∧
  cotangentSumVFormula 12 7 ≤ ((cotangentSumVFormula_12_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_7_unfold]
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
  rw [cotangentSumVFormula_12_7_lower, cotangentSumVFormula_12_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_712_formula_bound :
  (((64797859275278656813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 12) ∧
  (vasyuninBEntryFormula 7 12 ≤ ((64798985175186186937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 12 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log12 := prim_log_12_bounds
  have b_Vhk := cotangentSumVFormula_7_12_bounds
  have b_Vkh := cotangentSumVFormula_12_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [cotangentSumVFormula_7_12_lower, cotangentSumVFormula_7_12_upper] at b_Vhk
  simp only [cotangentSumVFormula_12_7_lower, cotangentSumVFormula_12_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_12_unfold :
    cotangentSumVFormula 11 12 =
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
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_11_12_lower : ℚ := 2199837402785514817021 / 439804651110400000000
def cotangentSumVFormula_11_12_upper : ℚ := 2199837411581621901729 / 439804651110400000000
theorem cotangentSumVFormula_11_12_bounds :
  ((cotangentSumVFormula_11_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 12 ∧
  cotangentSumVFormula 11 12 ≤ ((cotangentSumVFormula_11_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_12_unfold]
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
  rw [cotangentSumVFormula_11_12_lower, cotangentSumVFormula_11_12_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_12_11_unfold :
    cotangentSumVFormula 12 11 =
      ((1/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 12 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_12_11_lower : ℚ := -947374301334035364927 / 219902325555200000000
def cotangentSumVFormula_12_11_upper : ℚ := -947374296935981041323 / 219902325555200000000
theorem cotangentSumVFormula_12_11_bounds :
  ((cotangentSumVFormula_12_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 11 ∧
  cotangentSumVFormula 12 11 ≤ ((cotangentSumVFormula_12_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_11_unfold]
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
  rw [cotangentSumVFormula_12_11_lower, cotangentSumVFormula_12_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1112_formula_bound :
  (((113991566770836454251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 12) ∧
  (vasyuninBEntryFormula 11 12 ≤ ((113993818570651295749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 12 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log12 := prim_log_12_bounds
  have b_Vhk := cotangentSumVFormula_11_12_bounds
  have b_Vkh := cotangentSumVFormula_12_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [cotangentSumVFormula_11_12_lower, cotangentSumVFormula_11_12_upper] at b_Vhk
  simp only [cotangentSumVFormula_12_11_lower, cotangentSumVFormula_12_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_13_unfold :
    cotangentSumVFormula 1 13 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_1_13_lower : ℚ := -2516650550571192214229 / 439804651110400000000
def cotangentSumVFormula_1_13_upper : ℚ := -2516650541775076535771 / 439804651110400000000
theorem cotangentSumVFormula_1_13_bounds :
  ((cotangentSumVFormula_1_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 13 ∧
  cotangentSumVFormula 1 13 ≤ ((cotangentSumVFormula_1_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_13_unfold]
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
  rw [cotangentSumVFormula_1_13_lower, cotangentSumVFormula_1_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_1_unfold :
    cotangentSumVFormula 13 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_13_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_13_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_13_1_bounds :
  ((cotangentSumVFormula_13_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 1 ∧
  cotangentSumVFormula 13 1 ≤ ((cotangentSumVFormula_13_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_1_unfold]
  rw [cotangentSumVFormula_13_1_lower, cotangentSumVFormula_13_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_113_formula_bound :
  (((52469809607817054969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 13) ∧
  (vasyuninBEntryFormula 1 13 ≤ ((52470372557773070031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_13_bounds
  have b_Vkh := cotangentSumVFormula_13_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_1_13_lower, cotangentSumVFormula_1_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_1_lower, cotangentSumVFormula_13_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_13_unfold :
    cotangentSumVFormula 2 13 =
      ((2/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_2_13_lower : ℚ := -1390755819028448464229 / 439804651110400000000
def cotangentSumVFormula_2_13_upper : ℚ := -1390755810232333567021 / 439804651110400000000
theorem cotangentSumVFormula_2_13_bounds :
  ((cotangentSumVFormula_2_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 13 ∧
  cotangentSumVFormula 2 13 ≤ ((cotangentSumVFormula_2_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_13_unfold]
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
  rw [cotangentSumVFormula_2_13_lower, cotangentSumVFormula_2_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_2_unfold :
    cotangentSumVFormula 13 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_13_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_13_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_13_2_bounds :
  ((cotangentSumVFormula_13_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 2 ∧
  cotangentSumVFormula 13 2 ≤ ((cotangentSumVFormula_13_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_13_2_lower, cotangentSumVFormula_13_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_213_formula_bound :
  (((44681061677006492469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 13) ∧
  (vasyuninBEntryFormula 2 13 ≤ ((44681624626961101281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_13_bounds
  have b_Vkh := cotangentSumVFormula_13_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_2_13_lower, cotangentSumVFormula_2_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_2_lower, cotangentSumVFormula_13_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_13_unfold :
    cotangentSumVFormula 3 13 =
      ((3/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_3_13_lower : ℚ := -705256799656117995479 / 439804651110400000000
def cotangentSumVFormula_3_13_upper : ℚ := -352628395430002135073 / 219902325555200000000
theorem cotangentSumVFormula_3_13_bounds :
  ((cotangentSumVFormula_3_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 13 ∧
  cotangentSumVFormula 3 13 ≤ ((cotangentSumVFormula_3_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_13_unfold]
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
  rw [cotangentSumVFormula_3_13_lower, cotangentSumVFormula_3_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_3_unfold :
    cotangentSumVFormula 13 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_13_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_13_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_13_3_bounds :
  ((cotangentSumVFormula_13_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 3 ∧
  cotangentSumVFormula 13 3 ≤ ((cotangentSumVFormula_13_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_13_3_lower, cotangentSumVFormula_13_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_313_formula_bound :
  (((80469307030937094313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 13) ∧
  (vasyuninBEntryFormula 3 13 ≤ ((80470432930845530687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_13_bounds
  have b_Vkh := cotangentSumVFormula_13_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_3_13_lower, cotangentSumVFormula_3_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_3_lower, cotangentSumVFormula_13_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_13_unfold :
    cotangentSumVFormula 4 13 =
      ((4/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_4_13_lower : ℚ := -2984200503054689880789 / 7036874417766400000000
def cotangentSumVFormula_4_13_upper : ℚ := -2984200362316891369211 / 7036874417766400000000
theorem cotangentSumVFormula_4_13_bounds :
  ((cotangentSumVFormula_4_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 13 ∧
  cotangentSumVFormula 4 13 ≤ ((cotangentSumVFormula_4_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_13_unfold]
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
  rw [cotangentSumVFormula_4_13_lower, cotangentSumVFormula_4_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_4_unfold :
    cotangentSumVFormula 13 4 =
      ((1/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((3/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_13_4_lower : ℚ := -1759218639625974041957 / 3518437208883200000000
def cotangentSumVFormula_13_4_upper : ℚ := -1759218569257223614293 / 3518437208883200000000
theorem cotangentSumVFormula_13_4_bounds :
  ((cotangentSumVFormula_13_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 4 ∧
  cotangentSumVFormula 13 4 ≤ ((cotangentSumVFormula_13_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_13_4_lower, cotangentSumVFormula_13_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_413_formula_bound :
  (((74300348850859469313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 13) ∧
  (vasyuninBEntryFormula 4 13 ≤ ((74301474750767405687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_13_bounds
  have b_Vkh := cotangentSumVFormula_13_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_4_13_lower, cotangentSumVFormula_4_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_4_lower, cotangentSumVFormula_13_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_13_unfold :
    cotangentSumVFormula 5 13 =
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
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_5_13_lower : ℚ := -2564725761354090662039 / 7036874417766400000000
def cotangentSumVFormula_5_13_upper : ℚ := -2564725620616296837961 / 7036874417766400000000
theorem cotangentSumVFormula_5_13_bounds :
  ((cotangentSumVFormula_5_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 13 ∧
  cotangentSumVFormula 5 13 ≤ ((cotangentSumVFormula_5_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_13_unfold]
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
  rw [cotangentSumVFormula_5_13_lower, cotangentSumVFormula_5_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_5_unfold :
    cotangentSumVFormula 13 5 =
      ((3/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_13_5_lower : ℚ := 2260935262917356492469 / 28147497671065600000000
def cotangentSumVFormula_13_5_upper : ℚ := 2260935825867424757531 / 28147497671065600000000
theorem cotangentSumVFormula_13_5_bounds :
  ((cotangentSumVFormula_13_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 5 ∧
  cotangentSumVFormula 13 5 ≤ ((cotangentSumVFormula_13_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_13_5_lower, cotangentSumVFormula_13_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_513_formula_bound :
  (((138055691086208141751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 13) ∧
  (vasyuninBEntryFormula 5 13 ≤ ((138057942886023639499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_13_bounds
  have b_Vkh := cotangentSumVFormula_13_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_5_13_lower, cotangentSumVFormula_5_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_5_lower, cotangentSumVFormula_13_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_13_unfold :
    cotangentSumVFormula 6 13 =
      ((6/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 6 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_6_13_lower : ℚ := 2528030260896387783709 / 1759218604441600000000
def cotangentSumVFormula_6_13_upper : ℚ := 2528030296080838778791 / 1759218604441600000000
theorem cotangentSumVFormula_6_13_bounds :
  ((cotangentSumVFormula_6_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 13 ∧
  cotangentSumVFormula 6 13 ≤ ((cotangentSumVFormula_6_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_13_unfold]
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
  rw [cotangentSumVFormula_6_13_lower, cotangentSumVFormula_6_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_6_unfold :
    cotangentSumVFormula 13 6 =
      ((1/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((5/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_13_6_lower : ℚ := -2369932465546953622541 / 1759218604441600000000
def cotangentSumVFormula_13_6_upper : ℚ := -2369932430362564346209 / 1759218604441600000000
theorem cotangentSumVFormula_13_6_bounds :
  ((cotangentSumVFormula_13_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 6 ∧
  cotangentSumVFormula 13 6 ≤ ((cotangentSumVFormula_13_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_6_unfold]
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
  rw [cotangentSumVFormula_13_6_lower, cotangentSumVFormula_13_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_613_formula_bound :
  (((4117868867072301793 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 13) ∧
  (vasyuninBEntryFormula 6 13 ≤ ((32943513886532257531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_13_bounds
  have b_Vkh := cotangentSumVFormula_13_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_6_13_lower, cotangentSumVFormula_6_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_6_lower, cotangentSumVFormula_13_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_13_unfold :
    cotangentSumVFormula 7 13 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_7_13_lower : ℚ := -632007574020206276729 / 439804651110400000000
def cotangentSumVFormula_7_13_upper : ℚ := -1264015130448186274667 / 879609302220800000000
theorem cotangentSumVFormula_7_13_bounds :
  ((cotangentSumVFormula_7_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 13 ∧
  cotangentSumVFormula 7 13 ≤ ((cotangentSumVFormula_7_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_13_unfold]
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
  rw [cotangentSumVFormula_7_13_lower, cotangentSumVFormula_7_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_7_unfold :
    cotangentSumVFormula 13 7 =
      ((6/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_13_7_lower : ℚ := 1633971105500482368417 / 879609302220800000000
def cotangentSumVFormula_13_7_upper : ℚ := 1633971123092677006583 / 879609302220800000000
theorem cotangentSumVFormula_13_7_bounds :
  ((cotangentSumVFormula_13_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 7 ∧
  cotangentSumVFormula 13 7 ≤ ((cotangentSumVFormula_13_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_7_unfold]
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
  rw [cotangentSumVFormula_13_7_lower, cotangentSumVFormula_13_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_713_formula_bound :
  (((62411614857668781813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 13) ∧
  (vasyuninBEntryFormula 7 13 ≤ ((15603185189394089703 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_7_13_bounds
  have b_Vkh := cotangentSumVFormula_13_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_7_13_lower, cotangentSumVFormula_7_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_7_lower, cotangentSumVFormula_13_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_13_unfold :
    cotangentSumVFormula 8 13 =
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
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_8_13_lower : ℚ := 80147675644260728823 / 219902325555200000000
def cotangentSumVFormula_8_13_upper : ℚ := 80147680042317396177 / 219902325555200000000
theorem cotangentSumVFormula_8_13_bounds :
  ((cotangentSumVFormula_8_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 13 ∧
  cotangentSumVFormula 8 13 ≤ ((cotangentSumVFormula_8_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_13_unfold]
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
  rw [cotangentSumVFormula_8_13_lower, cotangentSumVFormula_8_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_8_unfold :
    cotangentSumVFormula 13 8 =
      ((5/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_13_8_lower : ℚ := 728692187546585439959 / 1759218604441600000000
def cotangentSumVFormula_13_8_upper : ℚ := 728692222730973935041 / 1759218604441600000000
theorem cotangentSumVFormula_13_8_bounds :
  ((cotangentSumVFormula_13_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 8 ∧
  cotangentSumVFormula 13 8 ≤ ((cotangentSumVFormula_13_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_8_unfold]
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
  rw [cotangentSumVFormula_13_8_lower, cotangentSumVFormula_13_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_813_formula_bound :
  (((116919495588640798001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 13) ∧
  (vasyuninBEntryFormula 8 13 ≤ ((116921747388455733249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_8_13_bounds
  have b_Vkh := cotangentSumVFormula_13_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_8_13_lower, cotangentSumVFormula_8_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_8_lower, cotangentSumVFormula_13_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_13_unfold :
    cotangentSumVFormula 9 13 =
      ((9/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_9_13_lower : ℚ := 1492100181158468145543 / 3518437208883200000000
def cotangentSumVFormula_9_13_upper : ℚ := 1492100251527369354457 / 3518437208883200000000
theorem cotangentSumVFormula_9_13_bounds :
  ((cotangentSumVFormula_9_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 13 ∧
  cotangentSumVFormula 9 13 ≤ ((cotangentSumVFormula_9_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_13_unfold]
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
  rw [cotangentSumVFormula_9_13_lower, cotangentSumVFormula_9_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_9_unfold :
    cotangentSumVFormula 13 9 =
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
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_13_9_lower : ℚ := 927378290468754971209 / 1759218604441600000000
def cotangentSumVFormula_13_9_upper : ℚ := 927378325653165341291 / 1759218604441600000000
theorem cotangentSumVFormula_13_9_bounds :
  ((cotangentSumVFormula_13_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 9 ∧
  cotangentSumVFormula 13 9 ≤ ((cotangentSumVFormula_13_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_9_unfold]
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
  rw [cotangentSumVFormula_13_9_lower, cotangentSumVFormula_13_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_913_formula_bound :
  (((111988684137044110501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 13) ∧
  (vasyuninBEntryFormula 9 13 ≤ ((111990935936859108249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_9_13_bounds
  have b_Vkh := cotangentSumVFormula_13_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_9_13_lower, cotangentSumVFormula_9_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_9_lower, cotangentSumVFormula_13_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_13_unfold :
    cotangentSumVFormula 10 13 =
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
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 10 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_10_13_lower : ℚ := 1410513581720014399667 / 879609302220800000000
def cotangentSumVFormula_10_13_upper : ℚ := 705256799656120339229 / 439804651110400000000
theorem cotangentSumVFormula_10_13_bounds :
  ((cotangentSumVFormula_10_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 13 ∧
  cotangentSumVFormula 10 13 ≤ ((cotangentSumVFormula_10_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_13_unfold]
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
  rw [cotangentSumVFormula_10_13_lower, cotangentSumVFormula_10_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_10_unfold :
    cotangentSumVFormula 13 10 =
      ((3/10 : ℚ) : ℝ) * cotangentTermV 1 10    + 
      ((6/10 : ℚ) : ℝ) * cotangentTermV 2 10    + 
      ((9/10 : ℚ) : ℝ) * cotangentTermV 3 10    + 
      ((2/10 : ℚ) : ℝ) * cotangentTermV 4 10    + 
      ((5/10 : ℚ) : ℝ) * cotangentTermV 5 10    + 
      ((8/10 : ℚ) : ℝ) * cotangentTermV 6 10    + 
      ((1/10 : ℚ) : ℝ) * cotangentTermV 7 10    + 
      ((4/10 : ℚ) : ℝ) * cotangentTermV 8 10    + 
      ((7/10 : ℚ) : ℝ) * cotangentTermV 9 10 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_10]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_13_10_lower : ℚ := -2003802190385119354457 / 3518437208883200000000
def cotangentSumVFormula_13_10_upper : ℚ := -2003802120016316583043 / 3518437208883200000000
theorem cotangentSumVFormula_13_10_bounds :
  ((cotangentSumVFormula_13_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 10 ∧
  cotangentSumVFormula 13 10 ≤ ((cotangentSumVFormula_13_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_10_unfold]
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
  rw [cotangentSumVFormula_13_10_lower, cotangentSumVFormula_13_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1013_formula_bound :
  (((108083293336795548001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 13) ∧
  (vasyuninBEntryFormula 10 13 ≤ ((108085545136610358249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_10_13_bounds
  have b_Vkh := cotangentSumVFormula_13_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_10_13_lower, cotangentSumVFormula_10_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_10_lower, cotangentSumVFormula_13_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_13_unfold :
    cotangentSumVFormula 11 13 =
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
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_11_13_lower : ℚ := 1390755810232338254521 / 439804651110400000000
def cotangentSumVFormula_11_13_upper : ℚ := 1390755819028449245479 / 439804651110400000000
theorem cotangentSumVFormula_11_13_bounds :
  ((cotangentSumVFormula_11_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 13 ∧
  cotangentSumVFormula 11 13 ≤ ((cotangentSumVFormula_11_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_13_unfold]
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
  rw [cotangentSumVFormula_11_13_lower, cotangentSumVFormula_11_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_11_unfold :
    cotangentSumVFormula 13 11 =
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
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_13_11_lower : ℚ := -1924262803088862162833 / 879609302220800000000
def cotangentSumVFormula_13_11_upper : ℚ := -1924262785496647212167 / 879609302220800000000
theorem cotangentSumVFormula_13_11_bounds :
  ((cotangentSumVFormula_13_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 11 ∧
  cotangentSumVFormula 13 11 ≤ ((cotangentSumVFormula_13_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_11_unfold]
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
  rw [cotangentSumVFormula_13_11_lower, cotangentSumVFormula_13_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1113_formula_bound :
  (((105739121826128673001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 13) ∧
  (vasyuninBEntryFormula 11 13 ≤ ((105741373625943514499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_11_13_bounds
  have b_Vkh := cotangentSumVFormula_13_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_11_13_lower, cotangentSumVFormula_11_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_11_lower, cotangentSumVFormula_13_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_12_13_unfold :
    cotangentSumVFormula 12 13 =
      ((12/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 12 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_12_13_lower : ℚ := 1258325270887541197573 / 219902325555200000000
def cotangentSumVFormula_12_13_upper : ℚ := 1258325275285596302427 / 219902325555200000000
theorem cotangentSumVFormula_12_13_bounds :
  ((cotangentSumVFormula_12_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 13 ∧
  cotangentSumVFormula 12 13 ≤ ((cotangentSumVFormula_12_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_13_unfold]
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
  rw [cotangentSumVFormula_12_13_lower, cotangentSumVFormula_12_13_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_13_12_unfold :
    cotangentSumVFormula 13 12 =
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
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_13_12_lower : ℚ := -34372459555962836111 / 6871947673600000000
def cotangentSumVFormula_13_12_upper : ℚ := -1099918701392752135073 / 219902325555200000000
theorem cotangentSumVFormula_13_12_bounds :
  ((cotangentSumVFormula_13_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 12 ∧
  cotangentSumVFormula 13 12 ≤ ((cotangentSumVFormula_13_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_12_unfold]
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
  rw [cotangentSumVFormula_13_12_lower, cotangentSumVFormula_13_12_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1213_formula_bound :
  (((3289866792891895543 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 12 13) ∧
  (vasyuninBEntryFormula 12 13 ≤ ((26319497293088913781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 12 13 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log12 := prim_log_12_bounds
  have b_log13 := log_13_certified_bounds
  have b_Vhk := cotangentSumVFormula_12_13_bounds
  have b_Vkh := cotangentSumVFormula_13_12_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [cotangentSumVFormula_12_13_lower, cotangentSumVFormula_12_13_upper] at b_Vhk
  simp only [cotangentSumVFormula_13_12_lower, cotangentSumVFormula_13_12_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_14_unfold :
    cotangentSumVFormula 1 14 =
      ((1/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((3/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_1_14_lower : ℚ := -1422139090738335364927 / 219902325555200000000
def cotangentSumVFormula_1_14_upper : ℚ := -177767385792534202431 / 27487790694400000000
theorem cotangentSumVFormula_1_14_bounds :
  ((cotangentSumVFormula_1_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 14 ∧
  cotangentSumVFormula 1 14 ≤ ((cotangentSumVFormula_1_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_14_unfold]
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
  rw [cotangentSumVFormula_1_14_lower, cotangentSumVFormula_1_14_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_14_1_unfold :
    cotangentSumVFormula 14 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_14_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_14_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_14_1_bounds :
  ((cotangentSumVFormula_14_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 1 ∧
  cotangentSumVFormula 14 1 ≤ ((cotangentSumVFormula_14_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_1_unfold]
  rw [cotangentSumVFormula_14_1_lower, cotangentSumVFormula_14_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_114_formula_bound :
  (((24725901528798004047 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 14) ∧
  (vasyuninBEntryFormula 1 14 ≤ ((24726183003776214703 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 14 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log14 := prim_log_14_bounds
  have b_Vhk := cotangentSumVFormula_1_14_bounds
  have b_Vkh := cotangentSumVFormula_14_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [cotangentSumVFormula_1_14_lower, cotangentSumVFormula_1_14_upper] at b_Vhk
  simp only [cotangentSumVFormula_14_1_lower, cotangentSumVFormula_14_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_14_unfold :
    cotangentSumVFormula 3 14 =
      ((3/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((1/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_3_14_lower : ℚ := -1048026653573911745479 / 439804651110400000000
def cotangentSumVFormula_3_14_upper : ℚ := -1048026644777790598271 / 439804651110400000000
theorem cotangentSumVFormula_3_14_bounds :
  ((cotangentSumVFormula_3_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 14 ∧
  cotangentSumVFormula 3 14 ≤ ((cotangentSumVFormula_3_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_14_unfold]
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
  rw [cotangentSumVFormula_3_14_lower, cotangentSumVFormula_3_14_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_14_3_unfold :
    cotangentSumVFormula 14 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_14_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_14_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_14_3_bounds :
  ((cotangentSumVFormula_14_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 3 ∧
  cotangentSumVFormula 14 3 ≤ ((cotangentSumVFormula_14_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_14_3_lower, cotangentSumVFormula_14_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_314_formula_bound :
  (((38092548276496054969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 14) ∧
  (vasyuninBEntryFormula 3 14 ≤ ((9523277806612599539 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 14 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log14 := prim_log_14_bounds
  have b_Vhk := cotangentSumVFormula_3_14_bounds
  have b_Vkh := cotangentSumVFormula_14_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [cotangentSumVFormula_3_14_lower, cotangentSumVFormula_3_14_upper] at b_Vhk
  simp only [cotangentSumVFormula_14_3_lower, cotangentSumVFormula_14_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_14_unfold :
    cotangentSumVFormula 5 14 =
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
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_5_14_lower : ℚ := -2530551200052683310041 / 1759218604441600000000
def cotangentSumVFormula_5_14_upper : ℚ := -2530551164868205752459 / 1759218604441600000000
theorem cotangentSumVFormula_5_14_bounds :
  ((cotangentSumVFormula_5_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 14 ∧
  cotangentSumVFormula 5 14 ≤ ((cotangentSumVFormula_5_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_14_unfold]
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
  rw [cotangentSumVFormula_5_14_lower, cotangentSumVFormula_5_14_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_14_5_unfold :
    cotangentSumVFormula 14 5 =
      ((4/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_14_5_lower : ℚ := 3134269892212533770543 / 3518437208883200000000
def cotangentSumVFormula_14_5_upper : ℚ := 3134269962581292010707 / 3518437208883200000000
theorem cotangentSumVFormula_14_5_bounds :
  ((cotangentSumVFormula_14_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 5 ∧
  cotangentSumVFormula 14 5 ≤ ((cotangentSumVFormula_14_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_14_5_lower, cotangentSumVFormula_14_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_514_formula_bound :
  (((131941874989978079251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 14) ∧
  (vasyuninBEntryFormula 5 14 ≤ ((131944126789793826999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 14 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log14 := prim_log_14_bounds
  have b_Vhk := cotangentSumVFormula_5_14_bounds
  have b_Vkh := cotangentSumVFormula_14_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [cotangentSumVFormula_5_14_lower, cotangentSumVFormula_5_14_upper] at b_Vhk
  simp only [cotangentSumVFormula_14_5_lower, cotangentSumVFormula_14_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_14_unfold :
    cotangentSumVFormula 9 14 =
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
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_9_14_lower : ℚ := 632637791217057004521 / 439804651110400000000
def cotangentSumVFormula_9_14_upper : ℚ := 1265275600026344975333 / 879609302220800000000
theorem cotangentSumVFormula_9_14_bounds :
  ((cotangentSumVFormula_9_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 14 ∧
  cotangentSumVFormula 9 14 ≤ ((cotangentSumVFormula_9_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_14_unfold]
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
  rw [cotangentSumVFormula_9_14_lower, cotangentSumVFormula_9_14_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_14_9_unfold :
    cotangentSumVFormula 14 9 =
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
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_14_9_lower : ℚ := -927378325653162216291 / 1759218604441600000000
def cotangentSumVFormula_14_9_upper : ℚ := -927378290468754971209 / 1759218604441600000000
theorem cotangentSumVFormula_14_9_bounds :
  ((cotangentSumVFormula_14_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 9 ∧
  cotangentSumVFormula 14 9 ≤ ((cotangentSumVFormula_14_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_9_unfold]
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
  rw [cotangentSumVFormula_14_9_lower, cotangentSumVFormula_14_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_914_formula_bound :
  (((106883950135720891751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 14) ∧
  (vasyuninBEntryFormula 9 14 ≤ ((106886201935535858249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 14 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log14 := prim_log_14_bounds
  have b_Vhk := cotangentSumVFormula_9_14_bounds
  have b_Vkh := cotangentSumVFormula_14_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [cotangentSumVFormula_9_14_lower, cotangentSumVFormula_9_14_upper] at b_Vhk
  simp only [cotangentSumVFormula_14_9_lower, cotangentSumVFormula_14_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_14_unfold :
    cotangentSumVFormula 11 14 =
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
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_11_14_lower : ℚ := 2096053289555596430917 / 879609302220800000000
def cotangentSumVFormula_11_14_upper : ℚ := 2096053307147823881583 / 879609302220800000000
theorem cotangentSumVFormula_11_14_bounds :
  ((cotangentSumVFormula_11_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 14 ∧
  cotangentSumVFormula 11 14 ≤ ((cotangentSumVFormula_11_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_14_unfold]
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
  rw [cotangentSumVFormula_11_14_lower, cotangentSumVFormula_11_14_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_14_11_unfold :
    cotangentSumVFormula 14 11 =
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
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_14_11_lower : ℚ := -2230748134936280966291 / 1759218604441600000000
def cotangentSumVFormula_14_11_upper : ℚ := -2230748099751851064959 / 1759218604441600000000
theorem cotangentSumVFormula_14_11_bounds :
  ((cotangentSumVFormula_14_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 11 ∧
  cotangentSumVFormula 14 11 ≤ ((cotangentSumVFormula_14_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_11_unfold]
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
  rw [cotangentSumVFormula_14_11_lower, cotangentSumVFormula_14_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1114_formula_bound :
  (((99759736572663360501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 14) ∧
  (vasyuninBEntryFormula 11 14 ≤ ((99761988372478264499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 14 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log14 := prim_log_14_bounds
  have b_Vhk := cotangentSumVFormula_11_14_bounds
  have b_Vkh := cotangentSumVFormula_14_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [cotangentSumVFormula_11_14_lower, cotangentSumVFormula_11_14_upper] at b_Vhk
  simp only [cotangentSumVFormula_14_11_lower, cotangentSumVFormula_14_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_14_unfold :
    cotangentSumVFormula 13 14 =
      ((13/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((3/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((1/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_13_14_lower : ℚ := 1422139086340278697573 / 219902325555200000000
def cotangentSumVFormula_13_14_upper : ℚ := 355534772684583548263 / 54975581388800000000
theorem cotangentSumVFormula_13_14_bounds :
  ((cotangentSumVFormula_13_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 14 ∧
  cotangentSumVFormula 13 14 ≤ ((cotangentSumVFormula_13_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_14_unfold]
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
  rw [cotangentSumVFormula_13_14_lower, cotangentSumVFormula_13_14_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_14_13_unfold :
    cotangentSumVFormula 14 13 =
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
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_14_13_lower : ℚ := -2516650550571192214229 / 439804651110400000000
def cotangentSumVFormula_14_13_upper : ℚ := -2516650541775076535771 / 439804651110400000000
theorem cotangentSumVFormula_14_13_bounds :
  ((cotangentSumVFormula_14_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 13 ∧
  cotangentSumVFormula 14 13 ≤ ((cotangentSumVFormula_14_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_13_unfold]
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
  rw [cotangentSumVFormula_14_13_lower, cotangentSumVFormula_14_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1314_formula_bound :
  (((764174863411149667 / 8796093022208000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 14) ∧
  (vasyuninBEntryFormula 13 14 ≤ ((24454158579110507531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 14 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log14 := prim_log_14_bounds
  have b_Vhk := cotangentSumVFormula_13_14_bounds
  have b_Vkh := cotangentSumVFormula_14_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [cotangentSumVFormula_13_14_lower, cotangentSumVFormula_13_14_upper] at b_Vhk
  simp only [cotangentSumVFormula_14_13_lower, cotangentSumVFormula_14_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_15_unfold :
    cotangentSumVFormula 1 15 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_1_15_lower : ℚ := -1590970988452579896177 / 219902325555200000000
def cotangentSumVFormula_1_15_upper : ℚ := -397742746013629732987 / 54975581388800000000
theorem cotangentSumVFormula_1_15_bounds :
  ((cotangentSumVFormula_1_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 15 ∧
  cotangentSumVFormula 1 15 ≤ ((cotangentSumVFormula_1_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_15_unfold]
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
  rw [cotangentSumVFormula_1_15_lower, cotangentSumVFormula_1_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_1_unfold :
    cotangentSumVFormula 15 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_15_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_15_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_15_1_bounds :
  ((cotangentSumVFormula_15_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 1 ∧
  cotangentSumVFormula 15 1 ≤ ((cotangentSumVFormula_15_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_1_unfold]
  rw [cotangentSumVFormula_15_1_lower, cotangentSumVFormula_15_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_115_formula_bound :
  (((93580171186376344313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 15) ∧
  (vasyuninBEntryFormula 1 15 ≤ ((93581297086288780687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_1_15_bounds
  have b_Vkh := cotangentSumVFormula_15_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_1_15_lower, cotangentSumVFormula_1_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_1_lower, cotangentSumVFormula_15_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_15_unfold :
    cotangentSumVFormula 2 15 =
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
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_2_15_lower : ℚ := -1862559410021953932979 / 439804651110400000000
def cotangentSumVFormula_2_15_upper : ℚ := -1862559401225831223271 / 439804651110400000000
theorem cotangentSumVFormula_2_15_bounds :
  ((cotangentSumVFormula_2_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 15 ∧
  cotangentSumVFormula 2 15 ≤ ((cotangentSumVFormula_2_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_15_unfold]
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
  rw [cotangentSumVFormula_2_15_lower, cotangentSumVFormula_2_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_2_unfold :
    cotangentSumVFormula 15 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_15_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_15_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_15_2_bounds :
  ((cotangentSumVFormula_15_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 2 ∧
  cotangentSumVFormula 15 2 ≤ ((cotangentSumVFormula_15_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_15_2_lower, cotangentSumVFormula_15_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_215_formula_bound :
  (((80145256773895469313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 15) ∧
  (vasyuninBEntryFormula 2 15 ≤ ((80146382673805030687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_2_15_bounds
  have b_Vkh := cotangentSumVFormula_15_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_2_15_lower, cotangentSumVFormula_2_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_2_lower, cotangentSumVFormula_15_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_15_unfold :
    cotangentSumVFormula 4 15 =
      ((4/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_4_15_lower : ℚ := -901893767119739870479 / 439804651110400000000
def cotangentSumVFormula_4_15_upper : ℚ := -450946879161809166323 / 219902325555200000000
theorem cotangentSumVFormula_4_15_bounds :
  ((cotangentSumVFormula_4_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 15 ∧
  cotangentSumVFormula 4 15 ≤ ((cotangentSumVFormula_4_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_15_unfold]
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
  rw [cotangentSumVFormula_4_15_lower, cotangentSumVFormula_4_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_4_unfold :
    cotangentSumVFormula 15 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_15_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_15_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_15_4_bounds :
  ((cotangentSumVFormula_15_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 4 ∧
  cotangentSumVFormula 15 4 ≤ ((cotangentSumVFormula_15_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_15_4_lower, cotangentSumVFormula_15_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_415_formula_bound :
  (((33506553039703273719 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 15) ∧
  (vasyuninBEntryFormula 4 15 ≤ ((33507115989657320031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_4_15_bounds
  have b_Vkh := cotangentSumVFormula_15_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_4_15_lower, cotangentSumVFormula_4_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_4_lower, cotangentSumVFormula_15_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_15_unfold :
    cotangentSumVFormula 7 15 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_7_15_lower : ℚ := 1734058424179648774667 / 879609302220800000000
def cotangentSumVFormula_7_15_upper : ℚ := 1734058441771886381583 / 879609302220800000000
theorem cotangentSumVFormula_7_15_bounds :
  ((cotangentSumVFormula_7_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 15 ∧
  cotangentSumVFormula 7 15 ≤ ((cotangentSumVFormula_7_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_15_unfold]
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
  rw [cotangentSumVFormula_7_15_lower, cotangentSumVFormula_7_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_7_unfold :
    cotangentSumVFormula 15 7 =
      ((1/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_15_7_lower : ℚ := -3267942246185352841291 / 1759218604441600000000
def cotangentSumVFormula_15_7_upper : ℚ := -3267942211000966689959 / 1759218604441600000000
theorem cotangentSumVFormula_15_7_bounds :
  ((cotangentSumVFormula_15_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 7 ∧
  cotangentSumVFormula 15 7 ≤ ((cotangentSumVFormula_15_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_7_unfold]
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
  rw [cotangentSumVFormula_15_7_lower, cotangentSumVFormula_15_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_715_formula_bound :
  (((114089854584295735501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 15) ∧
  (vasyuninBEntryFormula 7 15 ≤ ((114092106384110951999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_7_15_bounds
  have b_Vkh := cotangentSumVFormula_15_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_7_15_lower, cotangentSumVFormula_7_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_7_lower, cotangentSumVFormula_15_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_15_unfold :
    cotangentSumVFormula 8 15 =
      ((8/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((4/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_8_15_lower : ℚ := -3468116883543758310041 / 1759218604441600000000
def cotangentSumVFormula_8_15_upper : ℚ := -3468116848359279189959 / 1759218604441600000000
theorem cotangentSumVFormula_8_15_bounds :
  ((cotangentSumVFormula_8_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 15 ∧
  cotangentSumVFormula 8 15 ≤ ((cotangentSumVFormula_8_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_15_unfold]
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
  rw [cotangentSumVFormula_8_15_lower, cotangentSumVFormula_8_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_8_unfold :
    cotangentSumVFormula 15 8 =
      ((7/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_15_8_lower : ℚ := 2123564698214891743417 / 879609302220800000000
def cotangentSumVFormula_15_8_upper : ℚ := 2123564715807086381583 / 879609302220800000000
theorem cotangentSumVFormula_15_8_bounds :
  ((cotangentSumVFormula_15_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 8 ∧
  cotangentSumVFormula 15 8 ≤ ((cotangentSumVFormula_15_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_8_unfold]
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
  rw [cotangentSumVFormula_15_8_lower, cotangentSumVFormula_15_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_815_formula_bound :
  (((108853691073229079251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 15) ∧
  (vasyuninBEntryFormula 8 15 ≤ ((108855942873044139499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_8_15_bounds
  have b_Vkh := cotangentSumVFormula_15_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_8_15_lower, cotangentSumVFormula_8_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_8_lower, cotangentSumVFormula_15_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_15_unfold :
    cotangentSumVFormula 11 15 =
      ((11/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((4/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_11_15_lower : ℚ := 450946879161812291323 / 219902325555200000000
def cotangentSumVFormula_11_15_upper : ℚ := 450946883559871302427 / 219902325555200000000
theorem cotangentSumVFormula_11_15_bounds :
  ((cotangentSumVFormula_11_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 15 ∧
  cotangentSumVFormula 11 15 ≤ ((cotangentSumVFormula_11_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_15_unfold]
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
  rw [cotangentSumVFormula_11_15_lower, cotangentSumVFormula_11_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_11_unfold :
    cotangentSumVFormula 15 11 =
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
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_15_11_lower : ℚ := -3098045053564121698207 / 3518437208883200000000
def cotangentSumVFormula_15_11_upper : ℚ := -3098044983195265801793 / 3518437208883200000000
theorem cotangentSumVFormula_15_11_bounds :
  ((cotangentSumVFormula_15_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 11 ∧
  cotangentSumVFormula 15 11 ≤ ((cotangentSumVFormula_15_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_11_unfold]
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
  rw [cotangentSumVFormula_15_11_lower, cotangentSumVFormula_15_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1115_formula_bound :
  (((47526805733424781813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 15) ∧
  (vasyuninBEntryFormula 11 15 ≤ ((47527931633332218187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_11_15_bounds
  have b_Vkh := cotangentSumVFormula_15_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_11_15_lower, cotangentSumVFormula_11_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_11_lower, cotangentSumVFormula_15_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_15_unfold :
    cotangentSumVFormula 13 15 =
      ((13/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((4/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_13_15_lower : ℚ := 1862559401225837473271 / 439804651110400000000
def cotangentSumVFormula_13_15_upper : ℚ := 1862559410021953932979 / 439804651110400000000
theorem cotangentSumVFormula_13_15_bounds :
  ((cotangentSumVFormula_13_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 15 ∧
  cotangentSumVFormula 13 15 ≤ ((cotangentSumVFormula_13_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_15_unfold]
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
  rw [cotangentSumVFormula_13_15_lower, cotangentSumVFormula_13_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_13_unfold :
    cotangentSumVFormula 15 13 =
      ((2/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_15_13_lower : ℚ := -1390755819028448464229 / 439804651110400000000
def cotangentSumVFormula_15_13_upper : ℚ := -1390755810232333567021 / 439804651110400000000
theorem cotangentSumVFormula_15_13_bounds :
  ((cotangentSumVFormula_15_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 13 ∧
  cotangentSumVFormula 15 13 ≤ ((cotangentSumVFormula_15_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_13_unfold]
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
  rw [cotangentSumVFormula_15_13_lower, cotangentSumVFormula_15_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1315_formula_bound :
  (((45673661990069406813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 15) ∧
  (vasyuninBEntryFormula 13 15 ≤ ((22837393944988413781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_13_15_bounds
  have b_Vkh := cotangentSumVFormula_15_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_13_15_lower, cotangentSumVFormula_13_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_13_lower, cotangentSumVFormula_15_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_14_15_unfold :
    cotangentSumVFormula 14 15 =
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
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 14 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_14_15_lower : ℚ := 1590970984054520885073 / 219902325555200000000
def cotangentSumVFormula_14_15_upper : ℚ := 397742747113145267013 / 54975581388800000000
theorem cotangentSumVFormula_14_15_bounds :
  ((cotangentSumVFormula_14_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 15 ∧
  cotangentSumVFormula 14 15 ≤ ((cotangentSumVFormula_14_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_15_unfold]
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
  rw [cotangentSumVFormula_14_15_lower, cotangentSumVFormula_14_15_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_15_14_unfold :
    cotangentSumVFormula 15 14 =
      ((1/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((3/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_15_14_lower : ℚ := -1422139090738335364927 / 219902325555200000000
def cotangentSumVFormula_15_14_upper : ℚ := -177767385792534202431 / 27487790694400000000
theorem cotangentSumVFormula_15_14_bounds :
  ((cotangentSumVFormula_15_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 14 ∧
  cotangentSumVFormula 15 14 ≤ ((cotangentSumVFormula_15_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_14_unfold]
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
  rw [cotangentSumVFormula_15_14_lower, cotangentSumVFormula_15_14_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1415_formula_bound :
  (((91352792289937298001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 14 15) ∧
  (vasyuninBEntryFormula 14 15 ≤ ((91355044089752358249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 14 15 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log14 := prim_log_14_bounds
  have b_log15 := prim_log_15_bounds
  have b_Vhk := cotangentSumVFormula_14_15_bounds
  have b_Vkh := cotangentSumVFormula_15_14_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [cotangentSumVFormula_14_15_lower, cotangentSumVFormula_14_15_upper] at b_Vhk
  simp only [cotangentSumVFormula_15_14_lower, cotangentSumVFormula_15_14_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_16_unfold :
    cotangentSumVFormula 1 16 =
      ((1/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_1_16_lower : ℚ := -1764484223855254114927 / 219902325555200000000
def cotangentSumVFormula_1_16_upper : ℚ := -1764484219457194322573 / 219902325555200000000
theorem cotangentSumVFormula_1_16_bounds :
  ((cotangentSumVFormula_1_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 16 ∧
  cotangentSumVFormula 1 16 ≤ ((cotangentSumVFormula_1_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_16_unfold]
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
  rw [cotangentSumVFormula_1_16_lower, cotangentSumVFormula_1_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_1_unfold :
    cotangentSumVFormula 16 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_16_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_16_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_16_1_bounds :
  ((cotangentSumVFormula_16_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 1 ∧
  cotangentSumVFormula 16 1 ≤ ((cotangentSumVFormula_16_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_1_unfold]
  rw [cotangentSumVFormula_16_1_lower, cotangentSumVFormula_16_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_116_formula_bound :
  (((88846669649864156813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 16) ∧
  (vasyuninBEntryFormula 1 16 ≤ ((88847795549775593187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_1_16_bounds
  have b_Vkh := cotangentSumVFormula_16_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_1_16_lower, cotangentSumVFormula_1_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_1_lower, cotangentSumVFormula_16_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_16_unfold :
    cotangentSumVFormula 3 16 =
      ((3/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_3_16_lower : ℚ := -628736123175440833677 / 219902325555200000000
def cotangentSumVFormula_3_16_upper : ℚ := -628736118777381041323 / 219902325555200000000
theorem cotangentSumVFormula_3_16_bounds :
  ((cotangentSumVFormula_3_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 16 ∧
  cotangentSumVFormula 3 16 ≤ ((cotangentSumVFormula_3_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_16_unfold]
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
  rw [cotangentSumVFormula_3_16_lower, cotangentSumVFormula_3_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_3_unfold :
    cotangentSumVFormula 16 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_16_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_16_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_16_3_bounds :
  ((cotangentSumVFormula_16_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 3 ∧
  cotangentSumVFormula 16 3 ≤ ((cotangentSumVFormula_16_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_16_3_lower, cotangentSumVFormula_16_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_316_formula_bound :
  (((138130273786444579251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 16) ∧
  (vasyuninBEntryFormula 3 16 ≤ ((138132525586261326999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_3_16_bounds
  have b_Vkh := cotangentSumVFormula_16_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_3_16_lower, cotangentSumVFormula_3_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_3_lower, cotangentSumVFormula_16_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_16_unfold :
    cotangentSumVFormula 5 16 =
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
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_5_16_lower : ℚ := -2847212483254487183453 / 14073748835532800000000
def cotangentSumVFormula_5_16_upper : ℚ := -2847212201778675316547 / 14073748835532800000000
theorem cotangentSumVFormula_5_16_bounds :
  ((cotangentSumVFormula_5_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 16 ∧
  cotangentSumVFormula 5 16 ≤ ((cotangentSumVFormula_5_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_16_unfold]
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
  rw [cotangentSumVFormula_5_16_lower, cotangentSumVFormula_5_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_5_unfold :
    cotangentSumVFormula 16 5 =
      ((1/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_16_5_lower : ℚ := -3134269962581291229457 / 3518437208883200000000
def cotangentSumVFormula_16_5_upper : ℚ := -3134269892212532208043 / 3518437208883200000000
theorem cotangentSumVFormula_16_5_bounds :
  ((cotangentSumVFormula_16_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 5 ∧
  cotangentSumVFormula 16 5 ≤ ((cotangentSumVFormula_16_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_16_5_lower, cotangentSumVFormula_16_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_516_formula_bound :
  (((30105872718386492469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 16) ∧
  (vasyuninBEntryFormula 5 16 ≤ ((60212871336680780687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_5_16_bounds
  have b_Vkh := cotangentSumVFormula_16_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_5_16_lower, cotangentSumVFormula_5_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_5_lower, cotangentSumVFormula_16_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_16_unfold :
    cotangentSumVFormula 7 16 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_7_16_lower : ℚ := 2226850521608540020543 / 3518437208883200000000
def cotangentSumVFormula_7_16_upper : ℚ := 2226850591977491229457 / 3518437208883200000000
theorem cotangentSumVFormula_7_16_bounds :
  ((cotangentSumVFormula_7_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 16 ∧
  cotangentSumVFormula 7 16 ≤ ((cotangentSumVFormula_7_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_16_unfold]
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
  rw [cotangentSumVFormula_7_16_lower, cotangentSumVFormula_7_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_7_unfold :
    cotangentSumVFormula 16 7 =
      ((2/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_16_7_lower : ℚ := -269592303162212526729 / 439804651110400000000
def cotangentSumVFormula_16_7_upper : ℚ := -539184588732231587167 / 879609302220800000000
theorem cotangentSumVFormula_16_7_bounds :
  ((cotangentSumVFormula_16_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 7 ∧
  cotangentSumVFormula 16 7 ≤ ((cotangentSumVFormula_16_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_7_unfold]
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
  rw [cotangentSumVFormula_16_7_lower, cotangentSumVFormula_16_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_716_formula_bound :
  (((27006868479696617469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 16) ∧
  (vasyuninBEntryFormula 7 16 ≤ ((54014862859300780687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_7_16_bounds
  have b_Vkh := cotangentSumVFormula_16_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_7_16_lower, cotangentSumVFormula_7_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_7_lower, cotangentSumVFormula_16_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_16_unfold :
    cotangentSumVFormula 9 16 =
      ((9/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_9_16_lower : ℚ := -556712647994365287833 / 879609302220800000000
def cotangentSumVFormula_9_16_upper : ℚ := -556712630402134712167 / 879609302220800000000
theorem cotangentSumVFormula_9_16_bounds :
  ((cotangentSumVFormula_9_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 16 ∧
  cotangentSumVFormula 9 16 ≤ ((cotangentSumVFormula_9_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_16_unfold]
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
  rw [cotangentSumVFormula_9_16_lower, cotangentSumVFormula_9_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_9_unfold :
    cotangentSumVFormula 16 9 =
      ((7/9 : ℚ) : ℝ) * cotangentTermV 1 9    + 
      ((5/9 : ℚ) : ℝ) * cotangentTermV 2 9    + 
      ((3/9 : ℚ) : ℝ) * cotangentTermV 3 9    + 
      ((1/9 : ℚ) : ℝ) * cotangentTermV 4 9    + 
      ((8/9 : ℚ) : ℝ) * cotangentTermV 5 9    + 
      ((6/9 : ℚ) : ℝ) * cotangentTermV 6 9    + 
      ((4/9 : ℚ) : ℝ) * cotangentTermV 7 9    + 
      ((2/9 : ℚ) : ℝ) * cotangentTermV 8 9 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_9]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_16_9_lower : ℚ := 584588387572393723271 / 439804651110400000000
def cotangentSumVFormula_16_9_upper : ℚ := 1169176792736990287833 / 879609302220800000000
theorem cotangentSumVFormula_16_9_bounds :
  ((cotangentSumVFormula_16_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 9 ∧
  cotangentSumVFormula 16 9 ≤ ((cotangentSumVFormula_16_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_9_unfold]
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
  rw [cotangentSumVFormula_16_9_lower, cotangentSumVFormula_16_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_916_formula_bound :
  (((98912007242597079251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 16) ∧
  (vasyuninBEntryFormula 9 16 ≤ ((98914259042411858249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_9_16_bounds
  have b_Vkh := cotangentSumVFormula_16_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_9_16_lower, cotangentSumVFormula_9_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_9_lower, cotangentSumVFormula_16_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_16_unfold :
    cotangentSumVFormula 11 16 =
      ((11/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_11_16_lower : ℚ := 1423606100889404650461 / 7036874417766400000000
def cotangentSumVFormula_11_16_upper : ℚ := 1423606241627242224539 / 7036874417766400000000
theorem cotangentSumVFormula_11_16_bounds :
  ((cotangentSumVFormula_11_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 16 ∧
  cotangentSumVFormula 11 16 ≤ ((cotangentSumVFormula_11_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_16_unfold]
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
  rw [cotangentSumVFormula_11_16_lower, cotangentSumVFormula_11_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_11_unfold :
    cotangentSumVFormula 16 11 =
      ((5/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_16_11_lower : ℚ := 1675571378290838564959 / 1759218604441600000000
def cotangentSumVFormula_16_11_upper : ℚ := 1675571413475262216291 / 1759218604441600000000
theorem cotangentSumVFormula_16_11_bounds :
  ((cotangentSumVFormula_16_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 11 ∧
  cotangentSumVFormula 16 11 ≤ ((cotangentSumVFormula_16_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_11_unfold]
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
  rw [cotangentSumVFormula_16_11_lower, cotangentSumVFormula_16_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1116_formula_bound :
  (((91275481140891641751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 16) ∧
  (vasyuninBEntryFormula 11 16 ≤ ((91277732940706389499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_11_16_bounds
  have b_Vkh := cotangentSumVFormula_16_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_11_16_lower, cotangentSumVFormula_11_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_11_lower, cotangentSumVFormula_16_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_16_unfold :
    cotangentSumVFormula 13 16 =
      ((13/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_13_16_lower : ℚ := 2514944475109533930917 / 879609302220800000000
def cotangentSumVFormula_13_16_upper : ℚ := 2514944492701760600333 / 879609302220800000000
theorem cotangentSumVFormula_13_16_bounds :
  ((cotangentSumVFormula_13_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 16 ∧
  cotangentSumVFormula 13 16 ≤ ((cotangentSumVFormula_13_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_16_unfold]
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
  rw [cotangentSumVFormula_13_16_lower, cotangentSumVFormula_13_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_13_unfold :
    cotangentSumVFormula 16 13 =
      ((3/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_16_13_lower : ℚ := -705256799656117995479 / 439804651110400000000
def cotangentSumVFormula_16_13_upper : ℚ := -352628395430002135073 / 219902325555200000000
theorem cotangentSumVFormula_16_13_bounds :
  ((cotangentSumVFormula_16_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 13 ∧
  cotangentSumVFormula 16 13 ≤ ((cotangentSumVFormula_16_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_13_unfold]
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
  rw [cotangentSumVFormula_16_13_lower, cotangentSumVFormula_16_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1316_formula_bound :
  (((86584101313704485501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 16) ∧
  (vasyuninBEntryFormula 13 16 ≤ ((86586353113519233249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_13_16_bounds
  have b_Vkh := cotangentSumVFormula_16_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_13_16_lower, cotangentSumVFormula_13_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_13_lower, cotangentSumVFormula_16_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_16_unfold :
    cotangentSumVFormula 15 16 =
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
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_15_16_lower : ℚ := 1764484219457194322573 / 219902325555200000000
def cotangentSumVFormula_15_16_upper : ℚ := 1764484223855254896177 / 219902325555200000000
theorem cotangentSumVFormula_15_16_bounds :
  ((cotangentSumVFormula_15_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 16 ∧
  cotangentSumVFormula 15 16 ≤ ((cotangentSumVFormula_15_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_16_unfold]
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
  rw [cotangentSumVFormula_15_16_lower, cotangentSumVFormula_15_16_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_16_15_unfold :
    cotangentSumVFormula 16 15 =
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
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_16_15_lower : ℚ := -1590970988452579896177 / 219902325555200000000
def cotangentSumVFormula_16_15_upper : ℚ := -397742746013629732987 / 54975581388800000000
theorem cotangentSumVFormula_16_15_bounds :
  ((cotangentSumVFormula_16_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 15 ∧
  cotangentSumVFormula 16 15 ≤ ((cotangentSumVFormula_16_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_15_unfold]
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
  rw [cotangentSumVFormula_16_15_lower, cotangentSumVFormula_16_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1516_formula_bound :
  (((42850602464867219313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 16) ∧
  (vasyuninBEntryFormula 15 16 ≤ ((42851728364774655687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 16 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log16 := prim_log_16_bounds
  have b_Vhk := cotangentSumVFormula_15_16_bounds
  have b_Vkh := cotangentSumVFormula_16_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [cotangentSumVFormula_15_16_lower, cotangentSumVFormula_15_16_upper] at b_Vhk
  simp only [cotangentSumVFormula_16_15_lower, cotangentSumVFormula_16_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_17_unfold :
    cotangentSumVFormula 1 17 =
      ((1/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_1_17_lower : ℚ := -1942384522052435364927 / 219902325555200000000
def cotangentSumVFormula_1_17_upper : ℚ := -1942384517654369322573 / 219902325555200000000
theorem cotangentSumVFormula_1_17_bounds :
  ((cotangentSumVFormula_1_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 17 ∧
  cotangentSumVFormula 1 17 ≤ ((cotangentSumVFormula_1_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_17_unfold]
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
  rw [cotangentSumVFormula_1_17_lower, cotangentSumVFormula_1_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_1_unfold :
    cotangentSumVFormula 17 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_17_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_17_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_17_1_bounds :
  ((cotangentSumVFormula_17_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 1 ∧
  cotangentSumVFormula 17 1 ≤ ((cotangentSumVFormula_17_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_1_unfold]
  rw [cotangentSumVFormula_17_1_lower, cotangentSumVFormula_17_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_117_formula_bound :
  (((5287966784157676793 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 17) ∧
  (vasyuninBEntryFormula 1 17 ≤ ((10576074305804505789 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_17_bounds
  have b_Vkh := cotangentSumVFormula_17_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_1_17_lower, cotangentSumVFormula_1_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_1_lower, cotangentSumVFormula_17_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_17_unfold :
    cotangentSumVFormula 2 17 =
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
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 2 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_2_17_lower : ℚ := -2371761849596309401729 / 439804651110400000000
def cotangentSumVFormula_2_17_upper : ℚ := -2371761840800178098271 / 439804651110400000000
theorem cotangentSumVFormula_2_17_bounds :
  ((cotangentSumVFormula_2_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 17 ∧
  cotangentSumVFormula 2 17 ≤ ((cotangentSumVFormula_2_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_17_unfold]
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
  rw [cotangentSumVFormula_2_17_lower, cotangentSumVFormula_2_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_2_unfold :
    cotangentSumVFormula 17 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_17_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_17_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_17_2_bounds :
  ((cotangentSumVFormula_17_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 2 ∧
  cotangentSumVFormula 17 2 ≤ ((cotangentSumVFormula_17_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_17_2_lower, cotangentSumVFormula_17_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_217_formula_bound :
  (((72797441989451406813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 17) ∧
  (vasyuninBEntryFormula 2 17 ≤ ((72798567889361249437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_17_bounds
  have b_Vkh := cotangentSumVFormula_17_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_2_17_lower, cotangentSumVFormula_2_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_2_lower, cotangentSumVFormula_17_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_17_unfold :
    cotangentSumVFormula 3 17 =
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
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_3_17_lower : ℚ := -1628526273974807839229 / 439804651110400000000
def cotangentSumVFormula_3_17_upper : ℚ := -814263132589338072573 / 219902325555200000000
theorem cotangentSumVFormula_3_17_bounds :
  ((cotangentSumVFormula_3_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 17 ∧
  cotangentSumVFormula 3 17 ≤ ((cotangentSumVFormula_3_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_17_unfold]
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
  rw [cotangentSumVFormula_3_17_lower, cotangentSumVFormula_3_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_3_unfold :
    cotangentSumVFormula 17 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_17_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_17_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_17_3_bounds :
  ((cotangentSumVFormula_17_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 3 ∧
  cotangentSumVFormula 17 3 ≤ ((cotangentSumVFormula_17_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_17_3_lower, cotangentSumVFormula_17_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_317_formula_bound :
  (((131983357369443079251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 17) ∧
  (vasyuninBEntryFormula 3 17 ≤ ((131985609169260764499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_17_bounds
  have b_Vkh := cotangentSumVFormula_17_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_3_17_lower, cotangentSumVFormula_3_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_3_lower, cotangentSumVFormula_17_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_17_unfold :
    cotangentSumVFormula 4 17 =
      ((4/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 4 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_4_17_lower : ℚ := -3119076762861611435041 / 1759218604441600000000
def cotangentSumVFormula_4_17_upper : ℚ := -3119076727677090127459 / 1759218604441600000000
theorem cotangentSumVFormula_4_17_bounds :
  ((cotangentSumVFormula_4_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 17 ∧
  cotangentSumVFormula 4 17 ≤ ((cotangentSumVFormula_4_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_17_unfold]
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
  rw [cotangentSumVFormula_4_17_lower, cotangentSumVFormula_4_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_4_unfold :
    cotangentSumVFormula 17 4 =
      ((1/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((3/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_17_4_lower : ℚ := -1759218639625974041957 / 3518437208883200000000
def cotangentSumVFormula_17_4_upper : ℚ := -1759218569257223614293 / 3518437208883200000000
theorem cotangentSumVFormula_17_4_bounds :
  ((cotangentSumVFormula_17_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 4 ∧
  cotangentSumVFormula 17 4 ≤ ((cotangentSumVFormula_17_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_17_4_lower, cotangentSumVFormula_17_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_417_formula_bound :
  (((122562606853990079251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 17) ∧
  (vasyuninBEntryFormula 4 17 ≤ ((122564858653806639499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_17_bounds
  have b_Vkh := cotangentSumVFormula_17_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_4_17_lower, cotangentSumVFormula_4_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_4_lower, cotangentSumVFormula_17_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_17_unfold :
    cotangentSumVFormula 5 17 =
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
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_5_17_lower : ℚ := -2253702665312962997541 / 1759218604441600000000
def cotangentSumVFormula_5_17_upper : ℚ := -2253702630128444814959 / 1759218604441600000000
theorem cotangentSumVFormula_5_17_bounds :
  ((cotangentSumVFormula_5_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 17 ∧
  cotangentSumVFormula 5 17 ≤ ((cotangentSumVFormula_5_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_17_unfold]
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
  rw [cotangentSumVFormula_5_17_lower, cotangentSumVFormula_5_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_5_unfold :
    cotangentSumVFormula 17 5 =
      ((2/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_17_5_lower : ℚ := -2260935825867423195031 / 28147497671065600000000
def cotangentSumVFormula_17_5_upper : ℚ := -2260935262917351804969 / 28147497671065600000000
theorem cotangentSumVFormula_17_5_bounds :
  ((cotangentSumVFormula_17_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 5 ∧
  cotangentSumVFormula 17 5 ≤ ((cotangentSumVFormula_17_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_17_5_lower, cotangentSumVFormula_17_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_517_formula_bound :
  (((114749462581657329251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 17) ∧
  (vasyuninBEntryFormula 5 17 ≤ ((114751714381473389499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_17_bounds
  have b_Vkh := cotangentSumVFormula_17_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_5_17_lower, cotangentSumVFormula_5_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_5_lower, cotangentSumVFormula_17_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_17_unfold :
    cotangentSumVFormula 6 17 =
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
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 6 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_6_17_lower : ℚ := -909029662072531276729 / 439804651110400000000
def cotangentSumVFormula_6_17_upper : ℚ := -909029653276402317021 / 439804651110400000000
theorem cotangentSumVFormula_6_17_bounds :
  ((cotangentSumVFormula_6_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 17 ∧
  cotangentSumVFormula 6 17 ≤ ((cotangentSumVFormula_6_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_17_unfold]
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
  rw [cotangentSumVFormula_6_17_lower, cotangentSumVFormula_6_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_6_unfold :
    cotangentSumVFormula 17 6 =
      ((5/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((1/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_17_6_lower : ℚ := 148120776897660637849 / 109951162777600000000
def cotangentSumVFormula_17_6_upper : ℚ := 1184966232773477787833 / 879609302220800000000
theorem cotangentSumVFormula_17_6_bounds :
  ((cotangentSumVFormula_17_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 6 ∧
  cotangentSumVFormula 17 6 ≤ ((cotangentSumVFormula_17_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_6_unfold]
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
  rw [cotangentSumVFormula_17_6_lower, cotangentSumVFormula_17_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_617_formula_bound :
  (((109279384399208704251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 17) ∧
  (vasyuninBEntryFormula 6 17 ≤ ((109281636199024358249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_17_bounds
  have b_Vkh := cotangentSumVFormula_17_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_6_17_lower, cotangentSumVFormula_6_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_6_lower, cotangentSumVFormula_17_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_17_unfold :
    cotangentSumVFormula 7 17 =
      ((7/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_7_17_lower : ℚ := -2268486144405007068289 / 7036874417766400000000
def cotangentSumVFormula_7_17_upper : ℚ := -2268486003666980431711 / 7036874417766400000000
theorem cotangentSumVFormula_7_17_bounds :
  ((cotangentSumVFormula_7_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 17 ∧
  cotangentSumVFormula 7 17 ≤ ((cotangentSumVFormula_7_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_17_unfold]
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
  rw [cotangentSumVFormula_7_17_lower, cotangentSumVFormula_7_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_7_unfold :
    cotangentSumVFormula 17 7 =
      ((3/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_17_7_lower : ℚ := 154071743954285493417 / 879609302220800000000
def cotangentSumVFormula_17_7_upper : ℚ := 154071761546478569083 / 879609302220800000000
theorem cotangentSumVFormula_17_7_bounds :
  ((cotangentSumVFormula_17_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 7 ∧
  cotangentSumVFormula 17 7 ≤ ((cotangentSumVFormula_17_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_7_unfold]
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
  rw [cotangentSumVFormula_17_7_lower, cotangentSumVFormula_17_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_717_formula_bound :
  (((12917740382935910297 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 17) ∧
  (vasyuninBEntryFormula 7 17 ≤ ((6459010928956412039 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_7_17_bounds
  have b_Vkh := cotangentSumVFormula_17_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_7_17_lower, cotangentSumVFormula_7_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_7_lower, cotangentSumVFormula_17_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_17_unfold :
    cotangentSumVFormula 8 17 =
      ((8/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 8 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_8_17_lower : ℚ := 1120956386264885129521 / 439804651110400000000
def cotangentSumVFormula_8_17_upper : ℚ := 280239098765252643401 / 109951162777600000000
theorem cotangentSumVFormula_8_17_bounds :
  ((cotangentSumVFormula_8_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 17 ∧
  cotangentSumVFormula 8 17 ≤ ((cotangentSumVFormula_8_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_17_unfold]
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
  rw [cotangentSumVFormula_8_17_lower, cotangentSumVFormula_8_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_8_unfold :
    cotangentSumVFormula 17 8 =
      ((1/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_17_8_lower : ℚ := -530891178951771302427 / 219902325555200000000
def cotangentSumVFormula_17_8_upper : ℚ := -1061782349107446067021 / 439804651110400000000
theorem cotangentSumVFormula_17_8_bounds :
  ((cotangentSumVFormula_17_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 8 ∧
  cotangentSumVFormula 17 8 ≤ ((cotangentSumVFormula_17_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_8_unfold]
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
  rw [cotangentSumVFormula_17_8_lower, cotangentSumVFormula_17_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_817_formula_bound :
  (((50312881167675250563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 17) ∧
  (vasyuninBEntryFormula 8 17 ≤ ((25157003533791382531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_8_17_bounds
  have b_Vkh := cotangentSumVFormula_17_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_8_17_lower, cotangentSumVFormula_8_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_8_lower, cotangentSumVFormula_17_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_17_unfold :
    cotangentSumVFormula 9 17 =
      ((9/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_9_17_lower : ℚ := -2241912790122013725333 / 879609302220800000000
def cotangentSumVFormula_9_17_upper : ℚ := -2241912772529755024667 / 879609302220800000000
theorem cotangentSumVFormula_9_17_bounds :
  ((cotangentSumVFormula_9_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 17 ∧
  cotangentSumVFormula 9 17 ≤ ((cotangentSumVFormula_9_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_17_unfold]
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
  rw [cotangentSumVFormula_9_17_lower, cotangentSumVFormula_9_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_9_unfold :
    cotangentSumVFormula 17 9 =
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
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_17_9_lower : ℚ := 1324275632006511692021 / 439804651110400000000
def cotangentSumVFormula_17_9_upper : ℚ := 165534455100326517013 / 54975581388800000000
theorem cotangentSumVFormula_17_9_bounds :
  ((cotangentSumVFormula_17_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 9 ∧
  cotangentSumVFormula 17 9 ≤ ((cotangentSumVFormula_17_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_9_unfold]
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
  rw [cotangentSumVFormula_17_9_lower, cotangentSumVFormula_17_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_917_formula_bound :
  (((48267695996163250563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 17) ∧
  (vasyuninBEntryFormula 9 17 ≤ ((24134410948035413781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_9_17_bounds
  have b_Vkh := cotangentSumVFormula_17_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_9_17_lower, cotangentSumVFormula_9_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_9_lower, cotangentSumVFormula_17_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_17_unfold :
    cotangentSumVFormula 10 17 =
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
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 10 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_10_17_lower : ℚ := 2268486003667060119211 / 7036874417766400000000
def cotangentSumVFormula_10_17_upper : ℚ := 2268486144405121130789 / 7036874417766400000000
theorem cotangentSumVFormula_10_17_bounds :
  ((cotangentSumVFormula_10_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 17 ∧
  cotangentSumVFormula 10 17 ≤ ((cotangentSumVFormula_10_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_17_unfold]
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
  rw [cotangentSumVFormula_10_17_lower, cotangentSumVFormula_10_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_10_unfold :
    cotangentSumVFormula 17 10 =
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
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_17_10_lower : ℚ := 2003802120016315801793 / 3518437208883200000000
def cotangentSumVFormula_17_10_upper : ℚ := 2003802190385117791957 / 3518437208883200000000
theorem cotangentSumVFormula_17_10_bounds :
  ((cotangentSumVFormula_17_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 10 ∧
  cotangentSumVFormula 17 10 ≤ ((cotangentSumVFormula_17_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_10_unfold]
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
  rw [cotangentSumVFormula_17_10_lower, cotangentSumVFormula_17_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1017_formula_bound :
  (((91135561663927391751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 17) ∧
  (vasyuninBEntryFormula 10 17 ≤ ((91137813463742358249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_10_17_bounds
  have b_Vkh := cotangentSumVFormula_17_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_10_17_lower, cotangentSumVFormula_10_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_10_lower, cotangentSumVFormula_17_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_17_unfold :
    cotangentSumVFormula 11 17 =
      ((11/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_11_17_lower : ℚ := 909029653276409348271 / 439804651110400000000
def cotangentSumVFormula_11_17_upper : ℚ := 909029662072535182979 / 439804651110400000000
theorem cotangentSumVFormula_11_17_bounds :
  ((cotangentSumVFormula_11_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 17 ∧
  cotangentSumVFormula 11 17 ≤ ((cotangentSumVFormula_11_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_17_unfold]
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
  rw [cotangentSumVFormula_11_17_lower, cotangentSumVFormula_11_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_11_unfold :
    cotangentSumVFormula 17 11 =
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
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_17_11_lower : ℚ := -3351142826950507635707 / 3518437208883200000000
def cotangentSumVFormula_17_11_upper : ℚ := -3351142756581654864293 / 3518437208883200000000
theorem cotangentSumVFormula_17_11_bounds :
  ((cotangentSumVFormula_17_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 11 ∧
  cotangentSumVFormula 17 11 ≤ ((cotangentSumVFormula_17_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_11_unfold]
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
  rw [cotangentSumVFormula_17_11_lower, cotangentSumVFormula_17_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1117_formula_bound :
  (((87859670799818360501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 17) ∧
  (vasyuninBEntryFormula 11 17 ≤ ((87861922599633295749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_11_17_bounds
  have b_Vkh := cotangentSumVFormula_17_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_11_17_lower, cotangentSumVFormula_11_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_11_lower, cotangentSumVFormula_17_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_12_17_unfold :
    cotangentSumVFormula 12 17 =
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
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 12 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_12_17_lower : ℚ := 140856414383029387849 / 109951162777600000000
def cotangentSumVFormula_12_17_upper : ℚ := 1126851332656487944083 / 879609302220800000000
theorem cotangentSumVFormula_12_17_bounds :
  ((cotangentSumVFormula_12_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 17 ∧
  cotangentSumVFormula 12 17 ≤ ((cotangentSumVFormula_12_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_17_unfold]
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
  rw [cotangentSumVFormula_12_17_lower, cotangentSumVFormula_12_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_12_unfold :
    cotangentSumVFormula 17 12 =
      ((5/12 : ℚ) : ℝ) * cotangentTermV 1 12    + 
      ((10/12 : ℚ) : ℝ) * cotangentTermV 2 12    + 
      ((3/12 : ℚ) : ℝ) * cotangentTermV 3 12    + 
      ((8/12 : ℚ) : ℝ) * cotangentTermV 4 12    + 
      ((1/12 : ℚ) : ℝ) * cotangentTermV 5 12    + 
      ((6/12 : ℚ) : ℝ) * cotangentTermV 6 12    + 
      ((11/12 : ℚ) : ℝ) * cotangentTermV 7 12    + 
      ((4/12 : ℚ) : ℝ) * cotangentTermV 8 12    + 
      ((9/12 : ℚ) : ℝ) * cotangentTermV 9 12    + 
      ((2/12 : ℚ) : ℝ) * cotangentTermV 10 12    + 
      ((7/12 : ℚ) : ℝ) * cotangentTermV 11 12 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_12]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_17_12_lower : ℚ := 833686767119254270129 / 450359962737049600000000
def cotangentSumVFormula_17_12_upper : ℚ := 833695774338345729871 / 450359962737049600000000
theorem cotangentSumVFormula_17_12_bounds :
  ((cotangentSumVFormula_17_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 12 ∧
  cotangentSumVFormula 17 12 ≤ ((cotangentSumVFormula_17_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_12_unfold]
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
  rw [cotangentSumVFormula_17_12_lower, cotangentSumVFormula_17_12_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1217_formula_bound :
  (((84957942423151516751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 12 17) ∧
  (vasyuninBEntryFormula 12 17 ≤ ((84960194222966451999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 12 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log12 := prim_log_12_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_12_17_bounds
  have b_Vkh := cotangentSumVFormula_17_12_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_12_17_lower, cotangentSumVFormula_12_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_12_lower, cotangentSumVFormula_17_12_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_17_unfold :
    cotangentSumVFormula 13 17 =
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
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_13_17_lower : ℚ := 1559538363838561274667 / 879609302220800000000
def cotangentSumVFormula_13_17_upper : ℚ := 1559538381430812162833 / 879609302220800000000
theorem cotangentSumVFormula_13_17_bounds :
  ((cotangentSumVFormula_13_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 17 ∧
  cotangentSumVFormula 13 17 ≤ ((cotangentSumVFormula_13_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_17_unfold]
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
  rw [cotangentSumVFormula_13_17_lower, cotangentSumVFormula_13_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_13_unfold :
    cotangentSumVFormula 17 13 =
      ((4/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((6/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_17_13_lower : ℚ := -2984200503054689880789 / 7036874417766400000000
def cotangentSumVFormula_17_13_upper : ℚ := -2984200362316891369211 / 7036874417766400000000
theorem cotangentSumVFormula_17_13_bounds :
  ((cotangentSumVFormula_17_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 13 ∧
  cotangentSumVFormula 17 13 ≤ ((cotangentSumVFormula_17_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_13_unfold]
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
  rw [cotangentSumVFormula_17_13_lower, cotangentSumVFormula_17_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1317_formula_bound :
  (((82808715488202016751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 17) ∧
  (vasyuninBEntryFormula 13 17 ≤ ((82810967288016858249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_13_17_bounds
  have b_Vkh := cotangentSumVFormula_17_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_13_17_lower, cotangentSumVFormula_13_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_13_lower, cotangentSumVFormula_17_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_14_17_unfold :
    cotangentSumVFormula 14 17 =
      ((14/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 14 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_14_17_lower : ℚ := 3257052530357371430917 / 879609302220800000000
def cotangentSumVFormula_14_17_upper : ℚ := 3257052547949619194083 / 879609302220800000000
theorem cotangentSumVFormula_14_17_bounds :
  ((cotangentSumVFormula_14_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 17 ∧
  cotangentSumVFormula 14 17 ≤ ((cotangentSumVFormula_14_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_17_unfold]
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
  rw [cotangentSumVFormula_14_17_lower, cotangentSumVFormula_14_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_14_unfold :
    cotangentSumVFormula 17 14 =
      ((3/14 : ℚ) : ℝ) * cotangentTermV 1 14    + 
      ((6/14 : ℚ) : ℝ) * cotangentTermV 2 14    + 
      ((9/14 : ℚ) : ℝ) * cotangentTermV 3 14    + 
      ((12/14 : ℚ) : ℝ) * cotangentTermV 4 14    + 
      ((1/14 : ℚ) : ℝ) * cotangentTermV 5 14    + 
      ((4/14 : ℚ) : ℝ) * cotangentTermV 6 14    + 
      ((7/14 : ℚ) : ℝ) * cotangentTermV 7 14    + 
      ((10/14 : ℚ) : ℝ) * cotangentTermV 8 14    + 
      ((13/14 : ℚ) : ℝ) * cotangentTermV 9 14    + 
      ((2/14 : ℚ) : ℝ) * cotangentTermV 10 14    + 
      ((5/14 : ℚ) : ℝ) * cotangentTermV 11 14    + 
      ((8/14 : ℚ) : ℝ) * cotangentTermV 12 14    + 
      ((11/14 : ℚ) : ℝ) * cotangentTermV 13 14 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_14]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_17_14_lower : ℚ := -1048026653573911745479 / 439804651110400000000
def cotangentSumVFormula_17_14_upper : ℚ := -1048026644777790598271 / 439804651110400000000
theorem cotangentSumVFormula_17_14_bounds :
  ((cotangentSumVFormula_17_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 14 ∧
  cotangentSumVFormula 17 14 ≤ ((cotangentSumVFormula_17_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_14_unfold]
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
  rw [cotangentSumVFormula_17_14_lower, cotangentSumVFormula_17_14_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1417_formula_bound :
  (((20312890540046367469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 14 17) ∧
  (vasyuninBEntryFormula 14 17 ≤ ((20313453490000101281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 14 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log14 := prim_log_14_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_14_17_bounds
  have b_Vkh := cotangentSumVFormula_17_14_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_14_17_lower, cotangentSumVFormula_14_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_14_lower, cotangentSumVFormula_17_14_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_17_unfold :
    cotangentSumVFormula 15 17 =
      ((15/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((1/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 15 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_15_17_lower : ℚ := 148235115050011546181 / 27487790694400000000
def cotangentSumVFormula_15_17_upper : ℚ := 296470231199539017013 / 54975581388800000000
theorem cotangentSumVFormula_15_17_bounds :
  ((cotangentSumVFormula_15_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 17 ∧
  cotangentSumVFormula 15 17 ≤ ((cotangentSumVFormula_15_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_17_unfold]
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
  rw [cotangentSumVFormula_15_17_lower, cotangentSumVFormula_15_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_15_unfold :
    cotangentSumVFormula 17 15 =
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
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_17_15_lower : ℚ := -1862559410021953932979 / 439804651110400000000
def cotangentSumVFormula_17_15_upper : ℚ := -1862559401225831223271 / 439804651110400000000
theorem cotangentSumVFormula_17_15_bounds :
  ((cotangentSumVFormula_17_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 15 ∧
  cotangentSumVFormula 17 15 ≤ ((cotangentSumVFormula_17_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_15_unfold]
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
  rw [cotangentSumVFormula_17_15_lower, cotangentSumVFormula_17_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1517_formula_bound :
  (((80475388601249610501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 17) ∧
  (vasyuninBEntryFormula 15 17 ≤ ((80477640401064514499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_15_17_bounds
  have b_Vkh := cotangentSumVFormula_17_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_15_17_lower, cotangentSumVFormula_15_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_15_lower, cotangentSumVFormula_17_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_16_17_unfold :
    cotangentSumVFormula 16 17 =
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
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 16 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_16_17_lower : ℚ := 485596129413593014237 / 54975581388800000000
def cotangentSumVFormula_16_17_upper : ℚ := 485596130513109329513 / 54975581388800000000
theorem cotangentSumVFormula_16_17_bounds :
  ((cotangentSumVFormula_16_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 17 ∧
  cotangentSumVFormula 16 17 ≤ ((cotangentSumVFormula_16_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_17_unfold]
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
  rw [cotangentSumVFormula_16_17_lower, cotangentSumVFormula_16_17_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_17_16_unfold :
    cotangentSumVFormula 17 16 =
      ((1/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((3/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_17_16_lower : ℚ := -1764484223855254114927 / 219902325555200000000
def cotangentSumVFormula_17_16_upper : ℚ := -1764484219457194322573 / 219902325555200000000
theorem cotangentSumVFormula_17_16_bounds :
  ((cotangentSumVFormula_17_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 16 ∧
  cotangentSumVFormula 17 16 ≤ ((cotangentSumVFormula_17_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_16_unfold]
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
  rw [cotangentSumVFormula_17_16_lower, cotangentSumVFormula_17_16_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1617_formula_bound :
  (((40357632694536031813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 16 17) ∧
  (vasyuninBEntryFormula 16 17 ≤ ((20179379297221726281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 16 17 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log16 := prim_log_16_bounds
  have b_log17 := log_17_certified_bounds
  have b_Vhk := cotangentSumVFormula_16_17_bounds
  have b_Vkh := cotangentSumVFormula_17_16_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [cotangentSumVFormula_16_17_lower, cotangentSumVFormula_16_17_upper] at b_Vhk
  simp only [cotangentSumVFormula_17_16_lower, cotangentSumVFormula_17_16_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_18_unfold :
    cotangentSumVFormula 1 18 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_1_18_lower : ℚ := -2124412502007694739927 / 219902325555200000000
def cotangentSumVFormula_1_18_upper : ℚ := -2124412497609621666323 / 219902325555200000000
theorem cotangentSumVFormula_1_18_bounds :
  ((cotangentSumVFormula_1_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 18 ∧
  cotangentSumVFormula 1 18 ≤ ((cotangentSumVFormula_1_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_18_unfold]
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
  rw [cotangentSumVFormula_1_18_lower, cotangentSumVFormula_1_18_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_18_1_unfold :
    cotangentSumVFormula 18 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_18_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_18_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_18_1_bounds :
  ((cotangentSumVFormula_18_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 1 ∧
  cotangentSumVFormula 18 1 ≤ ((cotangentSumVFormula_18_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_1_unfold]
  rw [cotangentSumVFormula_18_1_lower, cotangentSumVFormula_18_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_118_formula_bound :
  (((80786835839833125563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 18) ∧
  (vasyuninBEntryFormula 1 18 ≤ ((80787961739747624437 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 18 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log18 := prim_log_18_bounds
  have b_Vhk := cotangentSumVFormula_1_18_bounds
  have b_Vkh := cotangentSumVFormula_18_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [cotangentSumVFormula_1_18_lower, cotangentSumVFormula_1_18_upper] at b_Vhk
  simp only [cotangentSumVFormula_18_1_lower, cotangentSumVFormula_18_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_18_unfold :
    cotangentSumVFormula 5 18 =
      ((5/18 : ℚ) : ℝ) * cotangentTermV 1 18    + 
      ((10/18 : ℚ) : ℝ) * cotangentTermV 2 18    + 
      ((15/18 : ℚ) : ℝ) * cotangentTermV 3 18    + 
      ((2/18 : ℚ) : ℝ) * cotangentTermV 4 18    + 
      ((7/18 : ℚ) : ℝ) * cotangentTermV 5 18    + 
      ((12/18 : ℚ) : ℝ) * cotangentTermV 6 18    + 
      ((17/18 : ℚ) : ℝ) * cotangentTermV 7 18    + 
      ((4/18 : ℚ) : ℝ) * cotangentTermV 8 18    + 
      ((9/18 : ℚ) : ℝ) * cotangentTermV 9 18    + 
      ((14/18 : ℚ) : ℝ) * cotangentTermV 10 18    + 
      ((1/18 : ℚ) : ℝ) * cotangentTermV 11 18    + 
      ((6/18 : ℚ) : ℝ) * cotangentTermV 12 18    + 
      ((11/18 : ℚ) : ℝ) * cotangentTermV 13 18    + 
      ((16/18 : ℚ) : ℝ) * cotangentTermV 14 18    + 
      ((3/18 : ℚ) : ℝ) * cotangentTermV 15 18    + 
      ((8/18 : ℚ) : ℝ) * cotangentTermV 16 18    + 
      ((13/18 : ℚ) : ℝ) * cotangentTermV 17 18 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_18]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_5_18_lower : ℚ := -3089117839981413778791 / 1759218604441600000000
def cotangentSumVFormula_5_18_upper : ℚ := -3089117804796854971209 / 1759218604441600000000
theorem cotangentSumVFormula_5_18_bounds :
  ((cotangentSumVFormula_5_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 18 ∧
  cotangentSumVFormula 5 18 ≤ ((cotangentSumVFormula_5_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_18_unfold]
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
  rw [cotangentSumVFormula_5_18_lower, cotangentSumVFormula_5_18_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_18_5_unfold :
    cotangentSumVFormula 18 5 =
      ((3/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_18_5_lower : ℚ := 2260935262917356492469 / 28147497671065600000000
def cotangentSumVFormula_18_5_upper : ℚ := 2260935825867424757531 / 28147497671065600000000
theorem cotangentSumVFormula_18_5_bounds :
  ((cotangentSumVFormula_18_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 5 ∧
  cotangentSumVFormula 18 5 ≤ ((cotangentSumVFormula_18_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_18_5_lower, cotangentSumVFormula_18_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_518_formula_bound :
  (((110132131088164891751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 18) ∧
  (vasyuninBEntryFormula 5 18 ≤ ((110134382887981201999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 18 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log18 := prim_log_18_bounds
  have b_Vhk := cotangentSumVFormula_5_18_bounds
  have b_Vkh := cotangentSumVFormula_18_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [cotangentSumVFormula_5_18_lower, cotangentSumVFormula_5_18_upper] at b_Vhk
  simp only [cotangentSumVFormula_18_5_lower, cotangentSumVFormula_18_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_18_unfold :
    cotangentSumVFormula 7 18 =
      ((7/18 : ℚ) : ℝ) * cotangentTermV 1 18    + 
      ((14/18 : ℚ) : ℝ) * cotangentTermV 2 18    + 
      ((3/18 : ℚ) : ℝ) * cotangentTermV 3 18    + 
      ((10/18 : ℚ) : ℝ) * cotangentTermV 4 18    + 
      ((17/18 : ℚ) : ℝ) * cotangentTermV 5 18    + 
      ((6/18 : ℚ) : ℝ) * cotangentTermV 6 18    + 
      ((13/18 : ℚ) : ℝ) * cotangentTermV 7 18    + 
      ((2/18 : ℚ) : ℝ) * cotangentTermV 8 18    + 
      ((9/18 : ℚ) : ℝ) * cotangentTermV 9 18    + 
      ((16/18 : ℚ) : ℝ) * cotangentTermV 10 18    + 
      ((5/18 : ℚ) : ℝ) * cotangentTermV 11 18    + 
      ((12/18 : ℚ) : ℝ) * cotangentTermV 12 18    + 
      ((1/18 : ℚ) : ℝ) * cotangentTermV 13 18    + 
      ((8/18 : ℚ) : ℝ) * cotangentTermV 14 18    + 
      ((15/18 : ℚ) : ℝ) * cotangentTermV 15 18    + 
      ((4/18 : ℚ) : ℝ) * cotangentTermV 16 18    + 
      ((11/18 : ℚ) : ℝ) * cotangentTermV 17 18 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_18]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_7_18_lower : ℚ := -2507300233925520777203 / 14073748835532800000000
def cotangentSumVFormula_7_18_upper : ℚ := -2507299952449116722797 / 14073748835532800000000
theorem cotangentSumVFormula_7_18_bounds :
  ((cotangentSumVFormula_7_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 18 ∧
  cotangentSumVFormula 7 18 ≤ ((cotangentSumVFormula_7_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_18_unfold]
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
  rw [cotangentSumVFormula_7_18_lower, cotangentSumVFormula_7_18_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_18_7_unfold :
    cotangentSumVFormula 18 7 =
      ((4/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_18_7_lower : ℚ := -2465148184743653589703 / 14073748835532800000000
def cotangentSumVFormula_18_7_upper : ℚ := -2465147903268565160297 / 14073748835532800000000
theorem cotangentSumVFormula_18_7_bounds :
  ((cotangentSumVFormula_18_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 7 ∧
  cotangentSumVFormula 18 7 ≤ ((cotangentSumVFormula_18_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_7_unfold]
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
  rw [cotangentSumVFormula_18_7_lower, cotangentSumVFormula_18_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_718_formula_bound :
  (((99352504157563016751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 18) ∧
  (vasyuninBEntryFormula 7 18 ≤ ((99354755957378608249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 18 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log18 := prim_log_18_bounds
  have b_Vhk := cotangentSumVFormula_7_18_bounds
  have b_Vkh := cotangentSumVFormula_18_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [cotangentSumVFormula_7_18_lower, cotangentSumVFormula_7_18_upper] at b_Vhk
  simp only [cotangentSumVFormula_18_7_lower, cotangentSumVFormula_18_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_18_unfold :
    cotangentSumVFormula 11 18 =
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
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_11_18_lower : ℚ := 2507299952449330004047 / 14073748835532800000000
def cotangentSumVFormula_11_18_upper : ℚ := 2507300233925582495953 / 14073748835532800000000
theorem cotangentSumVFormula_11_18_bounds :
  ((cotangentSumVFormula_11_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 18 ∧
  cotangentSumVFormula 11 18 ≤ ((cotangentSumVFormula_11_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_18_unfold]
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
  rw [cotangentSumVFormula_11_18_lower, cotangentSumVFormula_11_18_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_18_11_unfold :
    cotangentSumVFormula 18 11 =
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
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 18 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_18_11_lower : ℚ := 774511245798822212167 / 879609302220800000000
def cotangentSumVFormula_18_11_upper : ℚ := 774511263391034037833 / 879609302220800000000
theorem cotangentSumVFormula_18_11_bounds :
  ((cotangentSumVFormula_18_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 11 ∧
  cotangentSumVFormula 18 11 ≤ ((cotangentSumVFormula_18_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_11_unfold]
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
  rw [cotangentSumVFormula_18_11_lower, cotangentSumVFormula_18_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1118_formula_bound :
  (((5292855086659087961 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 18) ∧
  (vasyuninBEntryFormula 11 18 ≤ ((21171983296590101281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 18 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log18 := prim_log_18_bounds
  have b_Vhk := cotangentSumVFormula_11_18_bounds
  have b_Vkh := cotangentSumVFormula_18_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [cotangentSumVFormula_11_18_lower, cotangentSumVFormula_11_18_upper] at b_Vhk
  simp only [cotangentSumVFormula_18_11_lower, cotangentSumVFormula_18_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_18_unfold :
    cotangentSumVFormula 13 18 =
      ((13/18 : ℚ) : ℝ) * cotangentTermV 1 18    + 
      ((8/18 : ℚ) : ℝ) * cotangentTermV 2 18    + 
      ((3/18 : ℚ) : ℝ) * cotangentTermV 3 18    + 
      ((16/18 : ℚ) : ℝ) * cotangentTermV 4 18    + 
      ((11/18 : ℚ) : ℝ) * cotangentTermV 5 18    + 
      ((6/18 : ℚ) : ℝ) * cotangentTermV 6 18    + 
      ((1/18 : ℚ) : ℝ) * cotangentTermV 7 18    + 
      ((14/18 : ℚ) : ℝ) * cotangentTermV 8 18    + 
      ((9/18 : ℚ) : ℝ) * cotangentTermV 9 18    + 
      ((4/18 : ℚ) : ℝ) * cotangentTermV 10 18    + 
      ((17/18 : ℚ) : ℝ) * cotangentTermV 11 18    + 
      ((12/18 : ℚ) : ℝ) * cotangentTermV 12 18    + 
      ((7/18 : ℚ) : ℝ) * cotangentTermV 13 18    + 
      ((2/18 : ℚ) : ℝ) * cotangentTermV 14 18    + 
      ((15/18 : ℚ) : ℝ) * cotangentTermV 15 18    + 
      ((10/18 : ℚ) : ℝ) * cotangentTermV 16 18    + 
      ((5/18 : ℚ) : ℝ) * cotangentTermV 17 18 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_18]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_13_18_lower : ℚ := 772279451199222629521 / 439804651110400000000
def cotangentSumVFormula_13_18_upper : ℚ := 48267466249709547569 / 27487790694400000000
theorem cotangentSumVFormula_13_18_bounds :
  ((cotangentSumVFormula_13_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 18 ∧
  cotangentSumVFormula 13 18 ≤ ((cotangentSumVFormula_13_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_18_unfold]
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
  rw [cotangentSumVFormula_13_18_lower, cotangentSumVFormula_13_18_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_18_13_unfold :
    cotangentSumVFormula 18 13 =
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
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 18 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_18_13_lower : ℚ := -2564725761354090662039 / 7036874417766400000000
def cotangentSumVFormula_18_13_upper : ℚ := -2564725620616296837961 / 7036874417766400000000
theorem cotangentSumVFormula_18_13_bounds :
  ((cotangentSumVFormula_18_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 13 ∧
  cotangentSumVFormula 18 13 ≤ ((cotangentSumVFormula_18_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_13_unfold]
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
  rw [cotangentSumVFormula_18_13_lower, cotangentSumVFormula_18_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1318_formula_bound :
  (((79586271049352923001 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 18) ∧
  (vasyuninBEntryFormula 13 18 ≤ ((79588522849167826999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 18 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log18 := prim_log_18_bounds
  have b_Vhk := cotangentSumVFormula_13_18_bounds
  have b_Vkh := cotangentSumVFormula_18_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [cotangentSumVFormula_13_18_lower, cotangentSumVFormula_13_18_upper] at b_Vhk
  simp only [cotangentSumVFormula_18_13_lower, cotangentSumVFormula_18_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_18_unfold :
    cotangentSumVFormula 17 18 =
      ((17/18 : ℚ) : ℝ) * cotangentTermV 1 18    + 
      ((16/18 : ℚ) : ℝ) * cotangentTermV 2 18    + 
      ((15/18 : ℚ) : ℝ) * cotangentTermV 3 18    + 
      ((14/18 : ℚ) : ℝ) * cotangentTermV 4 18    + 
      ((13/18 : ℚ) : ℝ) * cotangentTermV 5 18    + 
      ((12/18 : ℚ) : ℝ) * cotangentTermV 6 18    + 
      ((11/18 : ℚ) : ℝ) * cotangentTermV 7 18    + 
      ((10/18 : ℚ) : ℝ) * cotangentTermV 8 18    + 
      ((9/18 : ℚ) : ℝ) * cotangentTermV 9 18    + 
      ((8/18 : ℚ) : ℝ) * cotangentTermV 10 18    + 
      ((7/18 : ℚ) : ℝ) * cotangentTermV 11 18    + 
      ((6/18 : ℚ) : ℝ) * cotangentTermV 12 18    + 
      ((5/18 : ℚ) : ℝ) * cotangentTermV 13 18    + 
      ((4/18 : ℚ) : ℝ) * cotangentTermV 14 18    + 
      ((3/18 : ℚ) : ℝ) * cotangentTermV 15 18    + 
      ((2/18 : ℚ) : ℝ) * cotangentTermV 16 18    + 
      ((1/18 : ℚ) : ℝ) * cotangentTermV 17 18 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_18]
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_17_18_lower : ℚ := 2124412497609627135073 / 219902325555200000000
def cotangentSumVFormula_17_18_upper : ℚ := 2124412502007693177427 / 219902325555200000000
theorem cotangentSumVFormula_17_18_bounds :
  ((cotangentSumVFormula_17_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 18 ∧
  cotangentSumVFormula 17 18 ≤ ((cotangentSumVFormula_17_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_18_unfold]
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
  rw [cotangentSumVFormula_17_18_lower, cotangentSumVFormula_17_18_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_18_17_unfold :
    cotangentSumVFormula 18 17 =
      ((1/17 : ℚ) : ℝ) * cotangentTermV 1 17    + 
      ((2/17 : ℚ) : ℝ) * cotangentTermV 2 17    + 
      ((3/17 : ℚ) : ℝ) * cotangentTermV 3 17    + 
      ((4/17 : ℚ) : ℝ) * cotangentTermV 4 17    + 
      ((5/17 : ℚ) : ℝ) * cotangentTermV 5 17    + 
      ((6/17 : ℚ) : ℝ) * cotangentTermV 6 17    + 
      ((7/17 : ℚ) : ℝ) * cotangentTermV 7 17    + 
      ((8/17 : ℚ) : ℝ) * cotangentTermV 8 17    + 
      ((9/17 : ℚ) : ℝ) * cotangentTermV 9 17    + 
      ((10/17 : ℚ) : ℝ) * cotangentTermV 10 17    + 
      ((11/17 : ℚ) : ℝ) * cotangentTermV 11 17    + 
      ((12/17 : ℚ) : ℝ) * cotangentTermV 12 17    + 
      ((13/17 : ℚ) : ℝ) * cotangentTermV 13 17    + 
      ((14/17 : ℚ) : ℝ) * cotangentTermV 14 17    + 
      ((15/17 : ℚ) : ℝ) * cotangentTermV 15 17    + 
      ((16/17 : ℚ) : ℝ) * cotangentTermV 16 17 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_17]
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 18 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_18_17_lower : ℚ := -1942384522052435364927 / 219902325555200000000
def cotangentSumVFormula_18_17_upper : ℚ := -1942384517654369322573 / 219902325555200000000
theorem cotangentSumVFormula_18_17_bounds :
  ((cotangentSumVFormula_18_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 17 ∧
  cotangentSumVFormula 18 17 ≤ ((cotangentSumVFormula_18_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_17_unfold]
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
  rw [cotangentSumVFormula_18_17_lower, cotangentSumVFormula_18_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1718_formula_bound :
  (((38141580024456375563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 18) ∧
  (vasyuninBEntryFormula 17 18 ≤ ((19071352962181913781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 18 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log18 := prim_log_18_bounds
  have b_Vhk := cotangentSumVFormula_17_18_bounds
  have b_Vkh := cotangentSumVFormula_18_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [cotangentSumVFormula_17_18_lower, cotangentSumVFormula_17_18_upper] at b_Vhk
  simp only [cotangentSumVFormula_18_17_lower, cotangentSumVFormula_18_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_19_unfold :
    cotangentSumVFormula 1 19 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_1_19_lower : ℚ := -2310337804999529896177 / 219902325555200000000
def cotangentSumVFormula_1_19_upper : ℚ := -2310337800601460728823 / 219902325555200000000
theorem cotangentSumVFormula_1_19_bounds :
  ((cotangentSumVFormula_1_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 19 ∧
  cotangentSumVFormula 1 19 ≤ ((cotangentSumVFormula_1_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_19_unfold]
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
  rw [cotangentSumVFormula_1_19_lower, cotangentSumVFormula_1_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_1_unfold :
    cotangentSumVFormula 19 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_19_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_19_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_19_1_bounds :
  ((cotangentSumVFormula_19_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 1 ∧
  cotangentSumVFormula 19 1 ≤ ((cotangentSumVFormula_19_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_1_unfold]
  rw [cotangentSumVFormula_19_1_lower, cotangentSumVFormula_19_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_119_formula_bound :
  (((38661988020274054969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 19) ∧
  (vasyuninBEntryFormula 1 19 ≤ ((38662550970230757531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_19_bounds
  have b_Vkh := cotangentSumVFormula_19_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_1_19_lower, cotangentSumVFormula_1_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_1_lower, cotangentSumVFormula_19_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_19_unfold :
    cotangentSumVFormula 2 19 =
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
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 2 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_2_19_lower : ℚ := -1456974933957273646177 / 219902325555200000000
def cotangentSumVFormula_2_19_upper : ℚ := -728487464779602044099 / 109951162777600000000
theorem cotangentSumVFormula_2_19_bounds :
  ((cotangentSumVFormula_2_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 19 ∧
  cotangentSumVFormula 2 19 ≤ ((cotangentSumVFormula_2_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_19_unfold]
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
  rw [cotangentSumVFormula_2_19_lower, cotangentSumVFormula_2_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_2_unfold :
    cotangentSumVFormula 19 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_19_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_19_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_19_2_bounds :
  ((cotangentSumVFormula_19_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 2 ∧
  cotangentSumVFormula 19 2 ≤ ((cotangentSumVFormula_19_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_19_2_lower, cotangentSumVFormula_19_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_219_formula_bound :
  (((133576875636274485501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 19) ∧
  (vasyuninBEntryFormula 2 19 ≤ ((133579127436094764499 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_19_bounds
  have b_Vkh := cotangentSumVFormula_19_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_2_19_lower, cotangentSumVFormula_2_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_2_lower, cotangentSumVFormula_19_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_19_unfold :
    cotangentSumVFormula 3 19 =
      ((3/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_3_19_lower : ℚ := -944345185222999427427 / 219902325555200000000
def cotangentSumVFormula_3_19_upper : ℚ := -944345180824929478823 / 219902325555200000000
theorem cotangentSumVFormula_3_19_bounds :
  ((cotangentSumVFormula_3_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 19 ∧
  cotangentSumVFormula 3 19 ≤ ((cotangentSumVFormula_3_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_19_unfold]
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
  rw [cotangentSumVFormula_3_19_lower, cotangentSumVFormula_3_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_3_unfold :
    cotangentSumVFormula 19 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_19_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_19_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_19_3_bounds :
  ((cotangentSumVFormula_19_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 3 ∧
  cotangentSumVFormula 19 3 ≤ ((cotangentSumVFormula_19_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_19_3_lower, cotangentSumVFormula_19_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_319_formula_bound :
  (((60724606595339813063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 19) ∧
  (vasyuninBEntryFormula 3 19 ≤ ((60725732495248780687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_19_bounds
  have b_Vkh := cotangentSumVFormula_19_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_3_19_lower, cotangentSumVFormula_3_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_3_lower, cotangentSumVFormula_19_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_19_unfold :
    cotangentSumVFormula 4 19 =
      ((4/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 4 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_4_19_lower : ℚ := -3132758945744026225333 / 879609302220800000000
def cotangentSumVFormula_4_19_upper : ℚ := -3132758928151751899667 / 879609302220800000000
theorem cotangentSumVFormula_4_19_bounds :
  ((cotangentSumVFormula_4_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 19 ∧
  cotangentSumVFormula 4 19 ≤ ((cotangentSumVFormula_4_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_19_unfold]
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
  rw [cotangentSumVFormula_4_19_lower, cotangentSumVFormula_4_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_4_unfold :
    cotangentSumVFormula 19 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_19_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_19_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_19_4_bounds :
  ((cotangentSumVFormula_19_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 4 ∧
  cotangentSumVFormula 19 4 ≤ ((cotangentSumVFormula_19_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_19_4_lower, cotangentSumVFormula_19_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_419_formula_bound :
  (((56446789886869000563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 19) ∧
  (vasyuninBEntryFormula 4 19 ≤ ((7055989473347162039 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_19_bounds
  have b_Vkh := cotangentSumVFormula_19_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_4_19_lower, cotangentSumVFormula_4_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_4_lower, cotangentSumVFormula_19_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_19_unfold :
    cotangentSumVFormula 5 19 =
      ((5/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 5 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_5_19_lower : ℚ := -2570819234437495756583 / 879609302220800000000
def cotangentSumVFormula_5_19_upper : ℚ := -2570819216845219868417 / 879609302220800000000
theorem cotangentSumVFormula_5_19_bounds :
  ((cotangentSumVFormula_5_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 19 ∧
  cotangentSumVFormula 5 19 ≤ ((cotangentSumVFormula_5_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_19_unfold]
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
  rw [cotangentSumVFormula_5_19_lower, cotangentSumVFormula_5_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_5_unfold :
    cotangentSumVFormula 19 5 =
      ((4/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_19_5_lower : ℚ := 3134269892212533770543 / 3518437208883200000000
def cotangentSumVFormula_19_5_upper : ℚ := 3134269962581292010707 / 3518437208883200000000
theorem cotangentSumVFormula_19_5_bounds :
  ((cotangentSumVFormula_19_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 5 ∧
  cotangentSumVFormula 19 5 ≤ ((cotangentSumVFormula_19_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_19_5_lower, cotangentSumVFormula_19_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_519_formula_bound :
  (((106361847410785454251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 19) ∧
  (vasyuninBEntryFormula 5 19 ≤ ((106364099210601670749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_19_bounds
  have b_Vkh := cotangentSumVFormula_19_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_5_19_lower, cotangentSumVFormula_5_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_5_lower, cotangentSumVFormula_19_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_19_unfold :
    cotangentSumVFormula 6 19 =
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
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 6 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_6_19_lower : ℚ := 2270957573391257273719 / 28147497671065600000000
def cotangentSumVFormula_6_19_upper : ℚ := 2270958136343992726281 / 28147497671065600000000
theorem cotangentSumVFormula_6_19_bounds :
  ((cotangentSumVFormula_6_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 19 ∧
  cotangentSumVFormula 6 19 ≤ ((cotangentSumVFormula_6_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_19_unfold]
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
  rw [cotangentSumVFormula_6_19_lower, cotangentSumVFormula_6_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_6_unfold :
    cotangentSumVFormula 19 6 =
      ((1/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((5/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_19_6_lower : ℚ := -2369932465546953622541 / 1759218604441600000000
def cotangentSumVFormula_19_6_upper : ℚ := -2369932430362564346209 / 1759218604441600000000
theorem cotangentSumVFormula_19_6_bounds :
  ((cotangentSumVFormula_19_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 6 ∧
  cotangentSumVFormula 19 6 ≤ ((cotangentSumVFormula_19_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_6_unfold]
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
  rw [cotangentSumVFormula_19_6_lower, cotangentSumVFormula_19_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_619_formula_bound :
  (((101282628533235454251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 19) ∧
  (vasyuninBEntryFormula 6 19 ≤ ((101284880333051233249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_19_bounds
  have b_Vkh := cotangentSumVFormula_19_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_6_19_lower, cotangentSumVFormula_6_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_6_lower, cotangentSumVFormula_19_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_19_unfold :
    cotangentSumVFormula 7 19 =
      ((7/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_7_19_lower : ℚ := -132682529281465143401 / 109951162777600000000
def cotangentSumVFormula_7_19_upper : ℚ := -530730108329723410771 / 439804651110400000000
theorem cotangentSumVFormula_7_19_bounds :
  ((cotangentSumVFormula_7_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 19 ∧
  cotangentSumVFormula 7 19 ≤ ((cotangentSumVFormula_7_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_19_unfold]
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
  rw [cotangentSumVFormula_7_19_lower, cotangentSumVFormula_7_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_7_unfold :
    cotangentSumVFormula 19 7 =
      ((5/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_19_7_lower : ℚ := 2156738354928926739293 / 3518437208883200000000
def cotangentSumVFormula_19_7_upper : ℚ := 2156738425297699041957 / 3518437208883200000000
theorem cotangentSumVFormula_19_7_bounds :
  ((cotangentSumVFormula_19_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 7 ∧
  cotangentSumVFormula 19 7 ≤ ((cotangentSumVFormula_19_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_7_unfold]
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
  rw [cotangentSumVFormula_19_7_lower, cotangentSumVFormula_19_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_719_formula_bound :
  (((95912840750173485501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 19) ∧
  (vasyuninBEntryFormula 7 19 ≤ ((95915092549988951999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_7_19_bounds
  have b_Vkh := cotangentSumVFormula_19_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_7_19_lower, cotangentSumVFormula_7_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_7_lower, cotangentSumVFormula_19_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_19_unfold :
    cotangentSumVFormula 8 19 =
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
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 8 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_8_19_lower : ℚ := 574043569585918252459 / 1759218604441600000000
def cotangentSumVFormula_8_19_upper : ℚ := 574043604770448935041 / 1759218604441600000000
theorem cotangentSumVFormula_8_19_bounds :
  ((cotangentSumVFormula_8_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 19 ∧
  cotangentSumVFormula 8 19 ≤ ((cotangentSumVFormula_8_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_19_unfold]
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
  rw [cotangentSumVFormula_8_19_lower, cotangentSumVFormula_8_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_8_unfold :
    cotangentSumVFormula 19 8 =
      ((3/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_19_8_lower : ℚ := -728692222730972372541 / 1759218604441600000000
def cotangentSumVFormula_19_8_upper : ℚ := -728692187546586221209 / 1759218604441600000000
theorem cotangentSumVFormula_19_8_bounds :
  ((cotangentSumVFormula_19_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 8 ∧
  cotangentSumVFormula 19 8 ≤ ((cotangentSumVFormula_19_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_8_unfold]
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
  rw [cotangentSumVFormula_19_8_lower, cotangentSumVFormula_19_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_819_formula_bound :
  (((11480638288238316547 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 19) ∧
  (vasyuninBEntryFormula 8 19 ≤ ((45923679052860811937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_8_19_bounds
  have b_Vkh := cotangentSumVFormula_19_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_8_19_lower, cotangentSumVFormula_8_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_8_lower, cotangentSumVFormula_19_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_19_unfold :
    cotangentSumVFormula 9 19 =
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
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_9_19_lower : ℚ := 2783035433767551899667 / 879609302220800000000
def cotangentSumVFormula_9_19_upper : ℚ := 2783035451359827787833 / 879609302220800000000
theorem cotangentSumVFormula_9_19_bounds :
  ((cotangentSumVFormula_9_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 19 ∧
  cotangentSumVFormula 9 19 ≤ ((cotangentSumVFormula_9_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_19_unfold]
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
  rw [cotangentSumVFormula_9_19_lower, cotangentSumVFormula_9_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_9_unfold :
    cotangentSumVFormula 19 9 =
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
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_19_9_lower : ℚ := -1324275640802612526729 / 439804651110400000000
def cotangentSumVFormula_19_9_upper : ℚ := -82767227000406858681 / 27487790694400000000
theorem cotangentSumVFormula_19_9_bounds :
  ((cotangentSumVFormula_19_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 9 ∧
  cotangentSumVFormula 19 9 ≤ ((cotangentSumVFormula_19_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_9_unfold]
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
  rw [cotangentSumVFormula_19_9_lower, cotangentSumVFormula_19_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_919_formula_bound :
  (((5626559810043681711 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 19) ∧
  (vasyuninBEntryFormula 9 19 ≤ ((45013604380257061937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_9_19_bounds
  have b_Vkh := cotangentSumVFormula_19_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_9_19_lower, cotangentSumVFormula_9_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_9_lower, cotangentSumVFormula_19_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_10_19_unfold :
    cotangentSumVFormula 10 19 =
      ((10/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 10 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_10_19_lower : ℚ := -2783035451359823881583 / 879609302220800000000
def cotangentSumVFormula_10_19_upper : ℚ := -2783035433767547993417 / 879609302220800000000
theorem cotangentSumVFormula_10_19_bounds :
  ((cotangentSumVFormula_10_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 19 ∧
  cotangentSumVFormula 10 19 ≤ ((cotangentSumVFormula_10_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_19_unfold]
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
  rw [cotangentSumVFormula_10_19_lower, cotangentSumVFormula_10_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_10_unfold :
    cotangentSumVFormula 19 10 =
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
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_19_10_lower : ℚ := 3204924154363070649667 / 879609302220800000000
def cotangentSumVFormula_19_10_upper : ℚ := 3204924171955274662833 / 879609302220800000000
theorem cotangentSumVFormula_19_10_bounds :
  ((cotangentSumVFormula_19_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 10 ∧
  cotangentSumVFormula 19 10 ≤ ((cotangentSumVFormula_19_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_10_unfold]
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
  rw [cotangentSumVFormula_19_10_lower, cotangentSumVFormula_19_10_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1019_formula_bound :
  (((86739647253921579251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 10 19) ∧
  (vasyuninBEntryFormula 10 19 ≤ ((86741899053736701999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 10 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log10 := prim_log_10_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_10_19_bounds
  have b_Vkh := cotangentSumVFormula_19_10_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_10_19_lower, cotangentSumVFormula_10_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_10_lower, cotangentSumVFormula_19_10_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_19_unfold :
    cotangentSumVFormula 11 19 =
      ((11/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_11_19_lower : ℚ := -1148087209540891229457 / 3518437208883200000000
def cotangentSumVFormula_11_19_upper : ℚ := -1148087139171805645543 / 3518437208883200000000
theorem cotangentSumVFormula_11_19_bounds :
  ((cotangentSumVFormula_11_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 19 ∧
  cotangentSumVFormula 11 19 ≤ ((cotangentSumVFormula_11_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_19_unfold]
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
  rw [cotangentSumVFormula_11_19_lower, cotangentSumVFormula_11_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_11_unfold :
    cotangentSumVFormula 19 11 =
      ((8/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((9/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_19_11_lower : ℚ := 1115374049875932368417 / 879609302220800000000
def cotangentSumVFormula_19_11_upper : ℚ := 1115374067468143412833 / 879609302220800000000
theorem cotangentSumVFormula_19_11_bounds :
  ((cotangentSumVFormula_19_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 11 ∧
  cotangentSumVFormula 19 11 ≤ ((cotangentSumVFormula_19_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_11_unfold]
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
  rw [cotangentSumVFormula_19_11_lower, cotangentSumVFormula_19_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1119_formula_bound :
  (((82122143169283516751 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 19) ∧
  (vasyuninBEntryFormula 11 19 ≤ ((82124394969098545749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_11_19_bounds
  have b_Vkh := cotangentSumVFormula_19_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_11_19_lower, cotangentSumVFormula_11_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_11_lower, cotangentSumVFormula_19_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_12_19_unfold :
    cotangentSumVFormula 12 19 =
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
  have hf_1 : Int.fract (((1 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 12 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_12_19_lower : ℚ := 2122920433318908096209 / 1759218604441600000000
def cotangentSumVFormula_12_19_upper : ℚ := 2122920468503440341291 / 1759218604441600000000
theorem cotangentSumVFormula_12_19_bounds :
  ((cotangentSumVFormula_12_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 12 19 ∧
  cotangentSumVFormula 12 19 ≤ ((cotangentSumVFormula_12_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_12_19_unfold]
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
  rw [cotangentSumVFormula_12_19_lower, cotangentSumVFormula_12_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_12_unfold :
    cotangentSumVFormula 19 12 =
      ((7/12 : ℚ) : ℝ) * cotangentTermV 1 12    + 
      ((2/12 : ℚ) : ℝ) * cotangentTermV 2 12    + 
      ((9/12 : ℚ) : ℝ) * cotangentTermV 3 12    + 
      ((4/12 : ℚ) : ℝ) * cotangentTermV 4 12    + 
      ((11/12 : ℚ) : ℝ) * cotangentTermV 5 12    + 
      ((6/12 : ℚ) : ℝ) * cotangentTermV 6 12    + 
      ((1/12 : ℚ) : ℝ) * cotangentTermV 7 12    + 
      ((8/12 : ℚ) : ℝ) * cotangentTermV 8 12    + 
      ((3/12 : ℚ) : ℝ) * cotangentTermV 9 12    + 
      ((10/12 : ℚ) : ℝ) * cotangentTermV 10 12    + 
      ((5/12 : ℚ) : ℝ) * cotangentTermV 11 12 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_12]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((7/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((2/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((9/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((4/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((11/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((6/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((1/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((8/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((3/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((10/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((12 : ℕ) : ℝ)) = ((5/12 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11]
  try ring

def cotangentSumVFormula_19_12_lower : ℚ := -3334783097327908310109 / 1801439850948198400000000
def cotangentSumVFormula_19_12_upper : ℚ := -3334747068459291689891 / 1801439850948198400000000
theorem cotangentSumVFormula_19_12_bounds :
  ((cotangentSumVFormula_19_12_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 12 ∧
  cotangentSumVFormula 19 12 ≤ ((cotangentSumVFormula_19_12_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_12_unfold]
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
  rw [cotangentSumVFormula_19_12_lower, cotangentSumVFormula_19_12_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1219_formula_bound :
  (((79203230044736454251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 12 19) ∧
  (vasyuninBEntryFormula 12 19 ≤ ((79205481844551420749 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 12 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log12 := prim_log_12_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_12_19_bounds
  have b_Vkh := cotangentSumVFormula_19_12_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_12_lower, prim_log_12_upper] at b_log12
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_12_19_lower, cotangentSumVFormula_12_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_12_lower, cotangentSumVFormula_19_12_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_19_unfold :
    cotangentSumVFormula 13 19 =
      ((13/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_13_19_lower : ℚ := -1135479068171862183453 / 14073748835532800000000
def cotangentSumVFormula_13_19_upper : ℚ := -1135478786695606566547 / 14073748835532800000000
theorem cotangentSumVFormula_13_19_bounds :
  ((cotangentSumVFormula_13_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 19 ∧
  cotangentSumVFormula 13 19 ≤ ((cotangentSumVFormula_13_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_19_unfold]
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
  rw [cotangentSumVFormula_13_19_lower, cotangentSumVFormula_13_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_13_unfold :
    cotangentSumVFormula 19 13 =
      ((6/13 : ℚ) : ℝ) * cotangentTermV 1 13    + 
      ((12/13 : ℚ) : ℝ) * cotangentTermV 2 13    + 
      ((5/13 : ℚ) : ℝ) * cotangentTermV 3 13    + 
      ((11/13 : ℚ) : ℝ) * cotangentTermV 4 13    + 
      ((4/13 : ℚ) : ℝ) * cotangentTermV 5 13    + 
      ((10/13 : ℚ) : ℝ) * cotangentTermV 6 13    + 
      ((3/13 : ℚ) : ℝ) * cotangentTermV 7 13    + 
      ((9/13 : ℚ) : ℝ) * cotangentTermV 8 13    + 
      ((2/13 : ℚ) : ℝ) * cotangentTermV 9 13    + 
      ((8/13 : ℚ) : ℝ) * cotangentTermV 10 13    + 
      ((1/13 : ℚ) : ℝ) * cotangentTermV 11 13    + 
      ((7/13 : ℚ) : ℝ) * cotangentTermV 12 13 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_13]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_19_13_lower : ℚ := 2528030260896387783709 / 1759218604441600000000
def cotangentSumVFormula_19_13_upper : ℚ := 2528030296080838778791 / 1759218604441600000000
theorem cotangentSumVFormula_19_13_bounds :
  ((cotangentSumVFormula_19_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 13 ∧
  cotangentSumVFormula 19 13 ≤ ((cotangentSumVFormula_19_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_13_unfold]
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
  rw [cotangentSumVFormula_19_13_lower, cotangentSumVFormula_19_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1319_formula_bound :
  (((38520672153431750563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 19) ∧
  (vasyuninBEntryFormula 13 19 ≤ ((38521798053339186937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_13_19_bounds
  have b_Vkh := cotangentSumVFormula_19_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_13_19_lower, cotangentSumVFormula_13_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_13_lower, cotangentSumVFormula_19_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_14_19_unfold :
    cotangentSumVFormula 14 19 =
      ((14/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 14 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_14_19_lower : ℚ := 2570819216845221430917 / 879609302220800000000
def cotangentSumVFormula_14_19_upper : ℚ := 2570819234437496537833 / 879609302220800000000
theorem cotangentSumVFormula_14_19_bounds :
  ((cotangentSumVFormula_14_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 14 19 ∧
  cotangentSumVFormula 14 19 ≤ ((cotangentSumVFormula_14_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_14_19_unfold]
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
  rw [cotangentSumVFormula_14_19_lower, cotangentSumVFormula_14_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_14_unfold :
    cotangentSumVFormula 19 14 =
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
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((5/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((10/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((1/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((6/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((11/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((2/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((7/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((12/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((3/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((8/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((13/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((4/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((14 : ℕ) : ℝ)) = ((9/14 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13]
  try ring

def cotangentSumVFormula_19_14_lower : ℚ := -2530551200052683310041 / 1759218604441600000000
def cotangentSumVFormula_19_14_upper : ℚ := -2530551164868205752459 / 1759218604441600000000
theorem cotangentSumVFormula_19_14_bounds :
  ((cotangentSumVFormula_19_14_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 14 ∧
  cotangentSumVFormula 19 14 ≤ ((cotangentSumVFormula_19_14_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_14_unfold]
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
  rw [cotangentSumVFormula_19_14_lower, cotangentSumVFormula_19_14_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1419_formula_bound :
  (((74943317695857235501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 14 19) ∧
  (vasyuninBEntryFormula 14 19 ≤ ((74945569495672201999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 14 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log14 := prim_log_14_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_14_19_bounds
  have b_Vkh := cotangentSumVFormula_19_14_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_14_lower, prim_log_14_upper] at b_log14
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_14_19_lower, cotangentSumVFormula_14_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_14_lower, cotangentSumVFormula_19_14_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_15_19_unfold :
    cotangentSumVFormula 15 19 =
      ((15/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((16/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 15 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_15_19_lower : ℚ := 1566379464075877317021 / 439804651110400000000
def cotangentSumVFormula_15_19_upper : ℚ := 783189736436007239927 / 219902325555200000000
theorem cotangentSumVFormula_15_19_bounds :
  ((cotangentSumVFormula_15_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 15 19 ∧
  cotangentSumVFormula 15 19 ≤ ((cotangentSumVFormula_15_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_15_19_unfold]
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
  rw [cotangentSumVFormula_15_19_lower, cotangentSumVFormula_15_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_15_unfold :
    cotangentSumVFormula 19 15 =
      ((4/15 : ℚ) : ℝ) * cotangentTermV 1 15    + 
      ((8/15 : ℚ) : ℝ) * cotangentTermV 2 15    + 
      ((12/15 : ℚ) : ℝ) * cotangentTermV 3 15    + 
      ((1/15 : ℚ) : ℝ) * cotangentTermV 4 15    + 
      ((5/15 : ℚ) : ℝ) * cotangentTermV 5 15    + 
      ((9/15 : ℚ) : ℝ) * cotangentTermV 6 15    + 
      ((13/15 : ℚ) : ℝ) * cotangentTermV 7 15    + 
      ((2/15 : ℚ) : ℝ) * cotangentTermV 8 15    + 
      ((6/15 : ℚ) : ℝ) * cotangentTermV 9 15    + 
      ((10/15 : ℚ) : ℝ) * cotangentTermV 10 15    + 
      ((14/15 : ℚ) : ℝ) * cotangentTermV 11 15    + 
      ((3/15 : ℚ) : ℝ) * cotangentTermV 12 15    + 
      ((7/15 : ℚ) : ℝ) * cotangentTermV 13 15    + 
      ((11/15 : ℚ) : ℝ) * cotangentTermV 14 15 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_15]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((4/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((8/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((12/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((1/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((5/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((9/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((13/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((2/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((6/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((10/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((14/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((3/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((7/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((15 : ℕ) : ℝ)) = ((11/15 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14]
  try ring

def cotangentSumVFormula_19_15_lower : ℚ := -901893767119739870479 / 439804651110400000000
def cotangentSumVFormula_19_15_upper : ℚ := -450946879161809166323 / 219902325555200000000
theorem cotangentSumVFormula_19_15_bounds :
  ((cotangentSumVFormula_19_15_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 15 ∧
  cotangentSumVFormula 19 15 ≤ ((cotangentSumVFormula_19_15_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_15_unfold]
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
  rw [cotangentSumVFormula_19_15_lower, cotangentSumVFormula_19_15_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1519_formula_bound :
  (((9177525777223222797 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 15 19) ∧
  (vasyuninBEntryFormula 15 19 ≤ ((9177807252200089703 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 15 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log15 := prim_log_15_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_15_19_bounds
  have b_Vkh := cotangentSumVFormula_19_15_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_15_lower, prim_log_15_upper] at b_log15
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_15_19_lower, cotangentSumVFormula_15_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_15_lower, cotangentSumVFormula_19_15_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_16_19_unfold :
    cotangentSumVFormula 16 19 =
      ((16/19 : ℚ) : ℝ) * cotangentTermV 1 19    + 
      ((13/19 : ℚ) : ℝ) * cotangentTermV 2 19    + 
      ((10/19 : ℚ) : ℝ) * cotangentTermV 3 19    + 
      ((7/19 : ℚ) : ℝ) * cotangentTermV 4 19    + 
      ((4/19 : ℚ) : ℝ) * cotangentTermV 5 19    + 
      ((1/19 : ℚ) : ℝ) * cotangentTermV 6 19    + 
      ((17/19 : ℚ) : ℝ) * cotangentTermV 7 19    + 
      ((14/19 : ℚ) : ℝ) * cotangentTermV 8 19    + 
      ((11/19 : ℚ) : ℝ) * cotangentTermV 9 19    + 
      ((8/19 : ℚ) : ℝ) * cotangentTermV 10 19    + 
      ((5/19 : ℚ) : ℝ) * cotangentTermV 11 19    + 
      ((2/19 : ℚ) : ℝ) * cotangentTermV 12 19    + 
      ((18/19 : ℚ) : ℝ) * cotangentTermV 13 19    + 
      ((15/19 : ℚ) : ℝ) * cotangentTermV 14 19    + 
      ((12/19 : ℚ) : ℝ) * cotangentTermV 15 19    + 
      ((9/19 : ℚ) : ℝ) * cotangentTermV 16 19    + 
      ((6/19 : ℚ) : ℝ) * cotangentTermV 17 19    + 
      ((3/19 : ℚ) : ℝ) * cotangentTermV 18 19 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_19]
  have hf_1 : Int.fract (((1 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 16 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_16_19_lower : ℚ := 1888690361649859348271 / 439804651110400000000
def cotangentSumVFormula_16_19_upper : ℚ := 1888690370445996901729 / 439804651110400000000
theorem cotangentSumVFormula_16_19_bounds :
  ((cotangentSumVFormula_16_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 16 19 ∧
  cotangentSumVFormula 16 19 ≤ ((cotangentSumVFormula_16_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_16_19_unfold]
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
  rw [cotangentSumVFormula_16_19_lower, cotangentSumVFormula_16_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_16_unfold :
    cotangentSumVFormula 19 16 =
      ((3/16 : ℚ) : ℝ) * cotangentTermV 1 16    + 
      ((6/16 : ℚ) : ℝ) * cotangentTermV 2 16    + 
      ((9/16 : ℚ) : ℝ) * cotangentTermV 3 16    + 
      ((12/16 : ℚ) : ℝ) * cotangentTermV 4 16    + 
      ((15/16 : ℚ) : ℝ) * cotangentTermV 5 16    + 
      ((2/16 : ℚ) : ℝ) * cotangentTermV 6 16    + 
      ((5/16 : ℚ) : ℝ) * cotangentTermV 7 16    + 
      ((8/16 : ℚ) : ℝ) * cotangentTermV 8 16    + 
      ((11/16 : ℚ) : ℝ) * cotangentTermV 9 16    + 
      ((14/16 : ℚ) : ℝ) * cotangentTermV 10 16    + 
      ((1/16 : ℚ) : ℝ) * cotangentTermV 11 16    + 
      ((4/16 : ℚ) : ℝ) * cotangentTermV 12 16    + 
      ((7/16 : ℚ) : ℝ) * cotangentTermV 13 16    + 
      ((10/16 : ℚ) : ℝ) * cotangentTermV 14 16    + 
      ((13/16 : ℚ) : ℝ) * cotangentTermV 15 16 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_16]
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((3/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((6/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((9/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((12/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((15/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((2/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((5/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((8/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((11/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((14/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((1/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((4/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((7/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((10/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((16 : ℕ) : ℝ)) = ((13/16 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15]
  try ring

def cotangentSumVFormula_19_16_lower : ℚ := -628736123175440833677 / 219902325555200000000
def cotangentSumVFormula_19_16_upper : ℚ := -628736118777381041323 / 219902325555200000000
theorem cotangentSumVFormula_19_16_bounds :
  ((cotangentSumVFormula_19_16_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 16 ∧
  cotangentSumVFormula 19 16 ≤ ((cotangentSumVFormula_19_16_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_16_unfold]
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
  rw [cotangentSumVFormula_19_16_lower, cotangentSumVFormula_19_16_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1619_formula_bound :
  (((36201109316793000563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 16 19) ∧
  (vasyuninBEntryFormula 16 19 ≤ ((36202235216700405687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 16 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log16 := prim_log_16_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_16_19_bounds
  have b_Vkh := cotangentSumVFormula_19_16_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_16_lower, prim_log_16_upper] at b_log16
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_16_19_lower, cotangentSumVFormula_16_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_16_lower, cotangentSumVFormula_19_16_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_19_unfold :
    cotangentSumVFormula 17 19 =
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
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_17_19_lower : ℚ := 2913949859118411692021 / 439804651110400000000
def cotangentSumVFormula_17_19_upper : ℚ := 2913949867914547682979 / 439804651110400000000
theorem cotangentSumVFormula_17_19_bounds :
  ((cotangentSumVFormula_17_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 19 ∧
  cotangentSumVFormula 17 19 ≤ ((cotangentSumVFormula_17_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_19_unfold]
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
  rw [cotangentSumVFormula_17_19_lower, cotangentSumVFormula_17_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_17_unfold :
    cotangentSumVFormula 19 17 =
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
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_19_17_lower : ℚ := -2371761849596309401729 / 439804651110400000000
def cotangentSumVFormula_19_17_upper : ℚ := -2371761840800178098271 / 439804651110400000000
theorem cotangentSumVFormula_19_17_bounds :
  ((cotangentSumVFormula_19_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 17 ∧
  cotangentSumVFormula 19 17 ≤ ((cotangentSumVFormula_19_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_17_unfold]
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
  rw [cotangentSumVFormula_19_17_lower, cotangentSumVFormula_19_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1719_formula_bound :
  (((71959609899589610501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 19) ∧
  (vasyuninBEntryFormula 17 19 ≤ ((71961861699404483249 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_17_19_bounds
  have b_Vkh := cotangentSumVFormula_19_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_17_19_lower, cotangentSumVFormula_17_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_17_lower, cotangentSumVFormula_19_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_18_19_unfold :
    cotangentSumVFormula 18 19 =
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
  have hf_1 : Int.fract (((1 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 18 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_18_19_lower : ℚ := 577584450150365670487 / 54975581388800000000
def cotangentSumVFormula_18_19_upper : ℚ := 144396112812470594097 / 13743895347200000000
theorem cotangentSumVFormula_18_19_bounds :
  ((cotangentSumVFormula_18_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 18 19 ∧
  cotangentSumVFormula 18 19 ≤ ((cotangentSumVFormula_18_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_18_19_unfold]
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
  rw [cotangentSumVFormula_18_19_lower, cotangentSumVFormula_18_19_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_19_18_unfold :
    cotangentSumVFormula 19 18 =
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
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((1/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((2/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((3/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((4/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((5/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((6/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((7/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((8/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((9/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((10/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((11/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((12/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((13/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((14/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((15/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((16/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((18 : ℕ) : ℝ)) = ((17/18 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17]
  try ring

def cotangentSumVFormula_19_18_lower : ℚ := -2124412502007694739927 / 219902325555200000000
def cotangentSumVFormula_19_18_upper : ℚ := -2124412497609621666323 / 219902325555200000000
theorem cotangentSumVFormula_19_18_bounds :
  ((cotangentSumVFormula_19_18_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 18 ∧
  cotangentSumVFormula 19 18 ≤ ((cotangentSumVFormula_19_18_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_18_unfold]
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
  rw [cotangentSumVFormula_19_18_lower, cotangentSumVFormula_19_18_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1819_formula_bound :
  (((36158451830651000563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 18 19) ∧
  (vasyuninBEntryFormula 18 19 ≤ ((9039894432639620953 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 18 19 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log18 := prim_log_18_bounds
  have b_log19 := log_19_certified_bounds
  have b_Vhk := cotangentSumVFormula_18_19_bounds
  have b_Vkh := cotangentSumVFormula_19_18_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_18_lower, prim_log_18_upper] at b_log18
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [cotangentSumVFormula_18_19_lower, cotangentSumVFormula_18_19_upper] at b_Vhk
  simp only [cotangentSumVFormula_19_18_lower, cotangentSumVFormula_19_18_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_20_unfold :
    cotangentSumVFormula 1 20 =
      ((1/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((9/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 1 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_1_20_lower : ℚ := -2499954472797344739927 / 219902325555200000000
def cotangentSumVFormula_1_20_upper : ℚ := -2499954468399269322573 / 219902325555200000000
theorem cotangentSumVFormula_1_20_bounds :
  ((cotangentSumVFormula_1_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 20 ∧
  cotangentSumVFormula 1 20 ≤ ((cotangentSumVFormula_1_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_20_unfold]
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
  rw [cotangentSumVFormula_1_20_lower, cotangentSumVFormula_1_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_1_unfold :
    cotangentSumVFormula 20 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_20_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_20_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_20_1_bounds :
  ((cotangentSumVFormula_20_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 1 ∧
  cotangentSumVFormula 20 1 ≤ ((cotangentSumVFormula_20_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_1_unfold]
  rw [cotangentSumVFormula_20_1_lower, cotangentSumVFormula_20_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_120_formula_bound :
  (((74169489622475938063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 20) ∧
  (vasyuninBEntryFormula 1 20 ≤ ((74170615522390186937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_1_20_bounds
  have b_Vkh := cotangentSumVFormula_20_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_1_20_lower, cotangentSumVFormula_1_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_1_lower, cotangentSumVFormula_20_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_20_unfold :
    cotangentSumVFormula 3 20 =
      ((3/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((9/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 3 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_3_20_lower : ℚ := -2283241528931042214229 / 439804651110400000000
def cotangentSumVFormula_3_20_upper : ℚ := -2283241520134892942021 / 439804651110400000000
theorem cotangentSumVFormula_3_20_bounds :
  ((cotangentSumVFormula_3_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 20 ∧
  cotangentSumVFormula 3 20 ≤ ((cotangentSumVFormula_3_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_20_unfold]
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
  rw [cotangentSumVFormula_3_20_lower, cotangentSumVFormula_3_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_3_unfold :
    cotangentSumVFormula 20 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_20_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_20_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_20_3_bounds :
  ((cotangentSumVFormula_20_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 3 ∧
  cotangentSumVFormula 20 3 ≤ ((cotangentSumVFormula_20_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_20_3_lower, cotangentSumVFormula_20_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_320_formula_bound :
  (((58401366858983938063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 20) ∧
  (vasyuninBEntryFormula 3 20 ≤ ((58402492758893218187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_3_20_bounds
  have b_Vkh := cotangentSumVFormula_20_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_3_20_lower, cotangentSumVFormula_3_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_3_lower, cotangentSumVFormula_20_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_20_unfold :
    cotangentSumVFormula 7 20 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 7 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_7_20_lower : ℚ := -2421372431136839506583 / 879609302220800000000
def cotangentSumVFormula_7_20_upper : ℚ := -2421372413544551118417 / 879609302220800000000
theorem cotangentSumVFormula_7_20_bounds :
  ((cotangentSumVFormula_7_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 20 ∧
  cotangentSumVFormula 7 20 ≤ ((cotangentSumVFormula_7_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_20_unfold]
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
  rw [cotangentSumVFormula_7_20_lower, cotangentSumVFormula_7_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_7_unfold :
    cotangentSumVFormula 20 7 =
      ((6/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_20_7_lower : ℚ := 1633971105500482368417 / 879609302220800000000
def cotangentSumVFormula_20_7_upper : ℚ := 1633971123092677006583 / 879609302220800000000
theorem cotangentSumVFormula_20_7_bounds :
  ((cotangentSumVFormula_20_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 7 ∧
  cotangentSumVFormula 20 7 ≤ ((cotangentSumVFormula_20_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_7_unfold]
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
  rw [cotangentSumVFormula_20_7_lower, cotangentSumVFormula_20_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_720_formula_bound :
  (((23324378600583961219 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 20) ∧
  (vasyuninBEntryFormula 7 20 ≤ ((11662470775268933453 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_7_20_bounds
  have b_Vkh := cotangentSumVFormula_20_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_7_20_lower, cotangentSumVFormula_7_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_7_lower, cotangentSumVFormula_20_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_20_unfold :
    cotangentSumVFormula 9 20 =
      ((9/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 9 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_9_20_lower : ℚ := 2505487595497696377459 / 1759218604441600000000
def cotangentSumVFormula_9_20_upper : ℚ := 2505487630682284872541 / 1759218604441600000000
theorem cotangentSumVFormula_9_20_bounds :
  ((cotangentSumVFormula_9_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 20 ∧
  cotangentSumVFormula 9 20 ≤ ((cotangentSumVFormula_9_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_20_unfold]
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
  rw [cotangentSumVFormula_9_20_lower, cotangentSumVFormula_9_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_9_unfold :
    cotangentSumVFormula 20 9 =
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
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_20_9_lower : ℚ := -1169176792736990287833 / 879609302220800000000
def cotangentSumVFormula_20_9_upper : ℚ := -1169176775144784712167 / 879609302220800000000
theorem cotangentSumVFormula_20_9_bounds :
  ((cotangentSumVFormula_20_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 9 ∧
  cotangentSumVFormula 20 9 ≤ ((cotangentSumVFormula_20_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_9_unfold]
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
  rw [cotangentSumVFormula_20_9_lower, cotangentSumVFormula_20_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_920_formula_bound :
  (((85933590754771329251 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 20) ∧
  (vasyuninBEntryFormula 9 20 ≤ ((85935842554586701999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_9_20_bounds
  have b_Vkh := cotangentSumVFormula_20_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_9_20_lower, cotangentSumVFormula_9_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_9_lower, cotangentSumVFormula_20_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_11_20_unfold :
    cotangentSumVFormula 11 20 =
      ((11/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((13/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((9/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 11 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_11_20_lower : ℚ := -2505487630682238778791 / 1759218604441600000000
def cotangentSumVFormula_11_20_upper : ℚ := -2505487595497698721209 / 1759218604441600000000
theorem cotangentSumVFormula_11_20_bounds :
  ((cotangentSumVFormula_11_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 11 20 ∧
  cotangentSumVFormula 11 20 ≤ ((cotangentSumVFormula_11_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_11_20_unfold]
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
  rw [cotangentSumVFormula_11_20_lower, cotangentSumVFormula_11_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_11_unfold :
    cotangentSumVFormula 20 11 =
      ((9/11 : ℚ) : ℝ) * cotangentTermV 1 11    + 
      ((7/11 : ℚ) : ℝ) * cotangentTermV 2 11    + 
      ((5/11 : ℚ) : ℝ) * cotangentTermV 3 11    + 
      ((3/11 : ℚ) : ℝ) * cotangentTermV 4 11    + 
      ((1/11 : ℚ) : ℝ) * cotangentTermV 5 11    + 
      ((10/11 : ℚ) : ℝ) * cotangentTermV 6 11    + 
      ((8/11 : ℚ) : ℝ) * cotangentTermV 7 11    + 
      ((6/11 : ℚ) : ℝ) * cotangentTermV 8 11    + 
      ((4/11 : ℚ) : ℝ) * cotangentTermV 9 11    + 
      ((2/11 : ℚ) : ℝ) * cotangentTermV 10 11 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_11]
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((9/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((7/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((5/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((3/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((1/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((10/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((8/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((6/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((4/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((11 : ℕ) : ℝ)) = ((2/11 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10]
  try ring

def cotangentSumVFormula_20_11_lower : ℚ := 962131392748326535771 / 439804651110400000000
def cotangentSumVFormula_20_11_upper : ℚ := 962131401544432839229 / 439804651110400000000
theorem cotangentSumVFormula_20_11_bounds :
  ((cotangentSumVFormula_20_11_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 11 ∧
  cotangentSumVFormula 20 11 ≤ ((cotangentSumVFormula_20_11_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_11_unfold]
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
  rw [cotangentSumVFormula_20_11_lower, cotangentSumVFormula_20_11_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1120_formula_bound :
  (((80095363888846360501 / 1125899906842624000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 11 20) ∧
  (vasyuninBEntryFormula 11 20 ≤ ((80097615688661326999 / 1125899906842624000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 11 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log11 := log_11_certified_bounds
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_11_20_bounds
  have b_Vkh := cotangentSumVFormula_20_11_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_11_lower, log_11_upper] at b_log11
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_11_20_lower, cotangentSumVFormula_11_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_11_lower, cotangentSumVFormula_20_11_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_13_20_unfold :
    cotangentSumVFormula 13 20 =
      ((13/20 : ℚ) : ℝ) * cotangentTermV 1 20    + 
      ((6/20 : ℚ) : ℝ) * cotangentTermV 2 20    + 
      ((19/20 : ℚ) : ℝ) * cotangentTermV 3 20    + 
      ((12/20 : ℚ) : ℝ) * cotangentTermV 4 20    + 
      ((5/20 : ℚ) : ℝ) * cotangentTermV 5 20    + 
      ((18/20 : ℚ) : ℝ) * cotangentTermV 6 20    + 
      ((11/20 : ℚ) : ℝ) * cotangentTermV 7 20    + 
      ((4/20 : ℚ) : ℝ) * cotangentTermV 8 20    + 
      ((17/20 : ℚ) : ℝ) * cotangentTermV 9 20    + 
      ((10/20 : ℚ) : ℝ) * cotangentTermV 10 20    + 
      ((3/20 : ℚ) : ℝ) * cotangentTermV 11 20    + 
      ((16/20 : ℚ) : ℝ) * cotangentTermV 12 20    + 
      ((9/20 : ℚ) : ℝ) * cotangentTermV 13 20    + 
      ((2/20 : ℚ) : ℝ) * cotangentTermV 14 20    + 
      ((15/20 : ℚ) : ℝ) * cotangentTermV 15 20    + 
      ((8/20 : ℚ) : ℝ) * cotangentTermV 16 20    + 
      ((1/20 : ℚ) : ℝ) * cotangentTermV 17 20    + 
      ((14/20 : ℚ) : ℝ) * cotangentTermV 18 20    + 
      ((7/20 : ℚ) : ℝ) * cotangentTermV 19 20 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_20]
  have hf_1 : Int.fract (((1 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 13 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_13_20_lower : ℚ := 2421372413544569087167 / 879609302220800000000
def cotangentSumVFormula_13_20_upper : ℚ := 2421372431136846537833 / 879609302220800000000
theorem cotangentSumVFormula_13_20_bounds :
  ((cotangentSumVFormula_13_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 13 20 ∧
  cotangentSumVFormula 13 20 ≤ ((cotangentSumVFormula_13_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_13_20_unfold]
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
  rw [cotangentSumVFormula_13_20_lower, cotangentSumVFormula_13_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_13_unfold :
    cotangentSumVFormula 20 13 =
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
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((7/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((1/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((8/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((2/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((9/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((3/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((10/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((4/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((11/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((5/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((12/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 20 : ℕ) : ℝ) / ((13 : ℕ) : ℝ)) = ((6/13 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12]
  try ring

def cotangentSumVFormula_20_13_lower : ℚ := -632007574020206276729 / 439804651110400000000
def cotangentSumVFormula_20_13_upper : ℚ := -1264015130448186274667 / 879609302220800000000
theorem cotangentSumVFormula_20_13_bounds :
  ((cotangentSumVFormula_20_13_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 13 ∧
  cotangentSumVFormula 20 13 ≤ ((cotangentSumVFormula_20_13_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_13_unfold]
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
  rw [cotangentSumVFormula_20_13_lower, cotangentSumVFormula_20_13_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1320_formula_bound :
  (((37297853787125656813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 13 20) ∧
  (vasyuninBEntryFormula 13 20 ≤ ((18649489843516570031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 13 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log13 := log_13_certified_bounds
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_13_20_bounds
  have b_Vkh := cotangentSumVFormula_20_13_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_13_lower, log_13_upper] at b_log13
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_13_20_lower, cotangentSumVFormula_13_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_13_lower, cotangentSumVFormula_20_13_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_17_20_unfold :
    cotangentSumVFormula 17 20 =
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
  have hf_1 : Int.fract (((1 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 17 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_17_20_lower : ℚ := 570810380033727044099 / 109951162777600000000
def cotangentSumVFormula_17_20_upper : ℚ := 142702595558190016319 / 27487790694400000000
theorem cotangentSumVFormula_17_20_bounds :
  ((cotangentSumVFormula_17_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 17 20 ∧
  cotangentSumVFormula 17 20 ≤ ((cotangentSumVFormula_17_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_17_20_unfold]
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
  rw [cotangentSumVFormula_17_20_lower, cotangentSumVFormula_17_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_17_unfold :
    cotangentSumVFormula 20 17 =
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
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((3/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((6/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((9/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((12/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((15/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((1/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((4/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((7/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((10/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((13/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((16/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((2/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((5/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((8/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((11/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 20 : ℕ) : ℝ) / ((17 : ℕ) : ℝ)) = ((14/17 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16]
  try ring

def cotangentSumVFormula_20_17_lower : ℚ := -1628526273974807839229 / 439804651110400000000
def cotangentSumVFormula_20_17_upper : ℚ := -814263132589338072573 / 219902325555200000000
theorem cotangentSumVFormula_20_17_bounds :
  ((cotangentSumVFormula_20_17_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 17 ∧
  cotangentSumVFormula 20 17 ≤ ((cotangentSumVFormula_20_17_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_17_unfold]
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
  rw [cotangentSumVFormula_20_17_lower, cotangentSumVFormula_20_17_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1720_formula_bound :
  (((137358141930750392877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 17 20) ∧
  (vasyuninBEntryFormula 17 20 ≤ ((137362645530379982123 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 17 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log17 := log_17_certified_bounds
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_17_20_bounds
  have b_Vkh := cotangentSumVFormula_20_17_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_17_lower, log_17_upper] at b_log17
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_17_20_lower, cotangentSumVFormula_17_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_17_lower, cotangentSumVFormula_20_17_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_19_20_unfold :
    cotangentSumVFormula 19 20 =
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
  have hf_1 : Int.fract (((1 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((19/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((18/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((17/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((16/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((15/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((14/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((13/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((12/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((11/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((10/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((9/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((8/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((7/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((6/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((5/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((4/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((3/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((2/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_19 : Int.fract (((19 * 19 : ℕ) : ℝ) / ((20 : ℕ) : ℝ)) = ((1/20 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18, hf_19]
  try ring

def cotangentSumVFormula_19_20_lower : ℚ := 1249977234199639544099 / 109951162777600000000
def cotangentSumVFormula_19_20_upper : ℚ := 624988618199335892013 / 54975581388800000000
theorem cotangentSumVFormula_19_20_bounds :
  ((cotangentSumVFormula_19_20_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 19 20 ∧
  cotangentSumVFormula 19 20 ≤ ((cotangentSumVFormula_19_20_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_19_20_unfold]
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
  rw [cotangentSumVFormula_19_20_lower, cotangentSumVFormula_19_20_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_20_19_unfold :
    cotangentSumVFormula 20 19 =
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
  have hf_1 : Int.fract (((1 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((1/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((2/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((3/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((4/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((5/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((6/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((7/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((8/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((9/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_10 : Int.fract (((10 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((10/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_11 : Int.fract (((11 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((11/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_12 : Int.fract (((12 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((12/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_13 : Int.fract (((13 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((13/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_14 : Int.fract (((14 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((14/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_15 : Int.fract (((15 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((15/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_16 : Int.fract (((16 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((16/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_17 : Int.fract (((17 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((17/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_18 : Int.fract (((18 * 20 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = ((18/19 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9, hf_10, hf_11, hf_12, hf_13, hf_14, hf_15, hf_16, hf_17, hf_18]
  try ring

def cotangentSumVFormula_20_19_lower : ℚ := -2310337804999529896177 / 219902325555200000000
def cotangentSumVFormula_20_19_upper : ℚ := -2310337800601460728823 / 219902325555200000000
theorem cotangentSumVFormula_20_19_bounds :
  ((cotangentSumVFormula_20_19_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 20 19 ∧
  cotangentSumVFormula 20 19 ≤ ((cotangentSumVFormula_20_19_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_20_19_unfold]
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
  rw [cotangentSumVFormula_20_19_lower, cotangentSumVFormula_20_19_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_1920_formula_bound :
  (((137492582564379892877 / 2251799813685248000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 19 20) ∧
  (vasyuninBEntryFormula 19 20 ≤ ((137497086164009388373 / 2251799813685248000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 19 20 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log19 := log_19_certified_bounds
  have b_log20 := prim_log_20_bounds
  have b_Vhk := cotangentSumVFormula_19_20_bounds
  have b_Vkh := cotangentSumVFormula_20_19_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_19_lower, log_19_upper] at b_log19
  simp only [prim_log_20_lower, prim_log_20_upper] at b_log20
  simp only [cotangentSumVFormula_19_20_lower, cotangentSumVFormula_19_20_upper] at b_Vhk
  simp only [cotangentSumVFormula_20_19_lower, cotangentSumVFormula_20_19_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
