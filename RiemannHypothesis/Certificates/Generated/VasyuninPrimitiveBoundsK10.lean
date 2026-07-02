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

theorem cotangentSumVFormula_1_2_unfold :
    cotangentSumVFormula 1 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_1_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_1_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_1_2_bounds :
  ((cotangentSumVFormula_1_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 2 ∧
  cotangentSumVFormula 1 2 ≤ ((cotangentSumVFormula_1_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_1_2_lower, cotangentSumVFormula_1_2_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_2_1_unfold :
    cotangentSumVFormula 2 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_2_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_2_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_2_1_bounds :
  ((cotangentSumVFormula_2_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 1 ∧
  cotangentSumVFormula 2 1 ≤ ((cotangentSumVFormula_2_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_1_unfold]
  rw [cotangentSumVFormula_2_1_lower, cotangentSumVFormula_2_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_12_formula_bound :
  (((108678650435403472797 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 2) ∧
  (vasyuninBEntryFormula 1 2 ≤ ((108678931910380433453 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 2 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_2_bounds
  have b_Vkh := cotangentSumVFormula_2_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [cotangentSumVFormula_1_2_lower, cotangentSumVFormula_1_2_upper] at b_Vhk
  simp only [cotangentSumVFormula_2_1_lower, cotangentSumVFormula_2_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_3_unfold :
    cotangentSumVFormula 1 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_1_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_1_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_1_3_bounds :
  ((cotangentSumVFormula_1_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 3 ∧
  cotangentSumVFormula 1 3 ≤ ((cotangentSumVFormula_1_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_1_3_lower, cotangentSumVFormula_1_3_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_3_1_unfold :
    cotangentSumVFormula 3 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_3_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_3_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_3_1_bounds :
  ((cotangentSumVFormula_3_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 1 ∧
  cotangentSumVFormula 3 1 ≤ ((cotangentSumVFormula_3_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_1_unfold]
  rw [cotangentSumVFormula_3_1_lower, cotangentSumVFormula_3_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_13_formula_bound :
  (((40462201675109337961 / 70368744177664000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 3) ∧
  (vasyuninBEntryFormula 1 3 ≤ ((2528896400787370479 / 4398046511104000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 3 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_3_bounds
  have b_Vkh := cotangentSumVFormula_3_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [cotangentSumVFormula_1_3_lower, cotangentSumVFormula_1_3_upper] at b_Vhk
  simp only [cotangentSumVFormula_3_1_lower, cotangentSumVFormula_3_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_3_unfold :
    cotangentSumVFormula 2 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_2_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_2_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_2_3_bounds :
  ((cotangentSumVFormula_2_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 3 ∧
  cotangentSumVFormula 2 3 ≤ ((cotangentSumVFormula_2_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_2_3_lower, cotangentSumVFormula_2_3_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_3_2_unfold :
    cotangentSumVFormula 3 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_3_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_3_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_3_2_bounds :
  ((cotangentSumVFormula_3_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 2 ∧
  cotangentSumVFormula 3 2 ≤ ((cotangentSumVFormula_3_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_3_2_lower, cotangentSumVFormula_3_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_23_formula_bound :
  (((124159318526431304969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 3) ∧
  (vasyuninBEntryFormula 2 3 ≤ ((124159881476385226281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 3 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_3_bounds
  have b_Vkh := cotangentSumVFormula_3_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [cotangentSumVFormula_2_3_lower, cotangentSumVFormula_2_3_upper] at b_Vhk
  simp only [cotangentSumVFormula_3_2_lower, cotangentSumVFormula_3_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_4_unfold :
    cotangentSumVFormula 1 4 =
      ((1/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((3/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_1_4_lower : ℚ := -1759218639625974041957 / 3518437208883200000000
def cotangentSumVFormula_1_4_upper : ℚ := -1759218569257223614293 / 3518437208883200000000
theorem cotangentSumVFormula_1_4_bounds :
  ((cotangentSumVFormula_1_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 4 ∧
  cotangentSumVFormula 1 4 ≤ ((cotangentSumVFormula_1_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_1_4_lower, cotangentSumVFormula_1_4_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_4_1_unfold :
    cotangentSumVFormula 4 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_4_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_4_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_4_1_bounds :
  ((cotangentSumVFormula_4_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 1 ∧
  cotangentSumVFormula 4 1 ≤ ((cotangentSumVFormula_4_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_1_unfold]
  rw [cotangentSumVFormula_4_1_lower, cotangentSumVFormula_4_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_14_formula_bound :
  (((130717410227266023719 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 4) ∧
  (vasyuninBEntryFormula 1 4 ≤ ((130717973177220070031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 4 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log4 := prim_log_4_bounds
  have b_Vhk := cotangentSumVFormula_1_4_bounds
  have b_Vkh := cotangentSumVFormula_4_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [cotangentSumVFormula_1_4_lower, cotangentSumVFormula_1_4_upper] at b_Vhk
  simp only [cotangentSumVFormula_4_1_lower, cotangentSumVFormula_4_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_4_unfold :
    cotangentSumVFormula 3 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_3_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_3_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_3_4_bounds :
  ((cotangentSumVFormula_3_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 4 ∧
  cotangentSumVFormula 3 4 ≤ ((cotangentSumVFormula_3_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_3_4_lower, cotangentSumVFormula_3_4_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_4_3_unfold :
    cotangentSumVFormula 4 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_4_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_4_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_4_3_bounds :
  ((cotangentSumVFormula_4_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 3 ∧
  cotangentSumVFormula 4 3 ≤ ((cotangentSumVFormula_4_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_4_3_lower, cotangentSumVFormula_4_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_34_formula_bound :
  (((88790427588746711219 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 4) ∧
  (vasyuninBEntryFormula 3 4 ≤ ((88790990538700538781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 4 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log4 := prim_log_4_bounds
  have b_Vhk := cotangentSumVFormula_3_4_bounds
  have b_Vkh := cotangentSumVFormula_4_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [cotangentSumVFormula_3_4_lower, cotangentSumVFormula_3_4_upper] at b_Vhk
  simp only [cotangentSumVFormula_4_3_lower, cotangentSumVFormula_4_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_5_unfold :
    cotangentSumVFormula 1 5 =
      ((1/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_1_5_lower : ℚ := -3134269962581291229457 / 3518437208883200000000
def cotangentSumVFormula_1_5_upper : ℚ := -3134269892212532208043 / 3518437208883200000000
theorem cotangentSumVFormula_1_5_bounds :
  ((cotangentSumVFormula_1_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 5 ∧
  cotangentSumVFormula 1 5 ≤ ((cotangentSumVFormula_1_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_1_5_lower, cotangentSumVFormula_1_5_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_5_1_unfold :
    cotangentSumVFormula 5 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_5_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_5_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_5_1_bounds :
  ((cotangentSumVFormula_5_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 1 ∧
  cotangentSumVFormula 5 1 ≤ ((cotangentSumVFormula_5_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_1_unfold]
  rw [cotangentSumVFormula_5_1_lower, cotangentSumVFormula_5_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_15_formula_bound :
  (((110472697161049804969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 5) ∧
  (vasyuninBEntryFormula 1 5 ≤ ((110473260111004195031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 5 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_5_bounds
  have b_Vkh := cotangentSumVFormula_5_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [cotangentSumVFormula_1_5_lower, cotangentSumVFormula_1_5_upper] at b_Vhk
  simp only [cotangentSumVFormula_5_1_lower, cotangentSumVFormula_5_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_5_unfold :
    cotangentSumVFormula 2 5 =
      ((2/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_2_5_lower : ℚ := -2260935825867423195031 / 28147497671065600000000
def cotangentSumVFormula_2_5_upper : ℚ := -2260935262917351804969 / 28147497671065600000000
theorem cotangentSumVFormula_2_5_bounds :
  ((cotangentSumVFormula_2_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 5 ∧
  cotangentSumVFormula 2 5 ≤ ((cotangentSumVFormula_2_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_2_5_lower, cotangentSumVFormula_2_5_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_5_2_unfold :
    cotangentSumVFormula 5 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_5_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_5_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_5_2_bounds :
  ((cotangentSumVFormula_5_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 2 ∧
  cotangentSumVFormula 5 2 ≤ ((cotangentSumVFormula_5_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_5_2_lower, cotangentSumVFormula_5_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_25_formula_bound :
  (((44529937215703254047 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 5) ∧
  (vasyuninBEntryFormula 2 5 ≤ ((22265109345340099539 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 5 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_5_bounds
  have b_Vkh := cotangentSumVFormula_5_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [cotangentSumVFormula_2_5_lower, cotangentSumVFormula_2_5_upper] at b_Vhk
  simp only [cotangentSumVFormula_5_2_lower, cotangentSumVFormula_5_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_5_unfold :
    cotangentSumVFormula 3 5 =
      ((3/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_3_5_lower : ℚ := 2260935262917356492469 / 28147497671065600000000
def cotangentSumVFormula_3_5_upper : ℚ := 2260935825867424757531 / 28147497671065600000000
theorem cotangentSumVFormula_3_5_bounds :
  ((cotangentSumVFormula_3_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 5 ∧
  cotangentSumVFormula 3 5 ≤ ((cotangentSumVFormula_3_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_3_5_lower, cotangentSumVFormula_3_5_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_5_3_unfold :
    cotangentSumVFormula 5 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_5_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_5_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_5_3_bounds :
  ((cotangentSumVFormula_5_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 3 ∧
  cotangentSumVFormula 5 3 ≤ ((cotangentSumVFormula_5_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_5_3_lower, cotangentSumVFormula_5_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_35_formula_bound :
  (((9624876281029645543 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 5) ∧
  (vasyuninBEntryFormula 3 5 ≤ ((38499786599095495953 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 5 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_5_bounds
  have b_Vkh := cotangentSumVFormula_5_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [cotangentSumVFormula_3_5_lower, cotangentSumVFormula_3_5_upper] at b_Vhk
  simp only [cotangentSumVFormula_5_3_lower, cotangentSumVFormula_5_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_5_unfold :
    cotangentSumVFormula 4 5 =
      ((4/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_4_5_lower : ℚ := 3134269892212533770543 / 3518437208883200000000
def cotangentSumVFormula_4_5_upper : ℚ := 3134269962581292010707 / 3518437208883200000000
theorem cotangentSumVFormula_4_5_bounds :
  ((cotangentSumVFormula_4_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 5 ∧
  cotangentSumVFormula 4 5 ≤ ((cotangentSumVFormula_4_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_4_5_lower, cotangentSumVFormula_4_5_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_5_4_unfold :
    cotangentSumVFormula 5 4 =
      ((1/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((3/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_5_4_lower : ℚ := -1759218639625974041957 / 3518437208883200000000
def cotangentSumVFormula_5_4_upper : ℚ := -1759218569257223614293 / 3518437208883200000000
theorem cotangentSumVFormula_5_4_bounds :
  ((cotangentSumVFormula_5_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 4 ∧
  cotangentSumVFormula 5 4 ≤ ((cotangentSumVFormula_5_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_5_4_lower, cotangentSumVFormula_5_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_45_formula_bound :
  (((8703728349987833043 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 5) ∧
  (vasyuninBEntryFormula 4 5 ≤ ((17407597437464099539 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 5 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_5_bounds
  have b_Vkh := cotangentSumVFormula_5_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [cotangentSumVFormula_4_5_lower, cotangentSumVFormula_4_5_upper] at b_Vhk
  simp only [cotangentSumVFormula_5_4_lower, cotangentSumVFormula_5_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_6_unfold :
    cotangentSumVFormula 1 6 =
      ((1/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((5/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_1_6_lower : ℚ := -2369932465546953622541 / 1759218604441600000000
def cotangentSumVFormula_1_6_upper : ℚ := -2369932430362564346209 / 1759218604441600000000
theorem cotangentSumVFormula_1_6_bounds :
  ((cotangentSumVFormula_1_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 6 ∧
  cotangentSumVFormula 1 6 ≤ ((cotangentSumVFormula_1_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_6_unfold]
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
  rw [cotangentSumVFormula_1_6_lower, cotangentSumVFormula_1_6_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_6_1_unfold :
    cotangentSumVFormula 6 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_6_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_6_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_6_1_bounds :
  ((cotangentSumVFormula_6_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 1 ∧
  cotangentSumVFormula 6 1 ≤ ((cotangentSumVFormula_6_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_1_unfold]
  rw [cotangentSumVFormula_6_1_lower, cotangentSumVFormula_6_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_16_formula_bound :
  (((96124149768815867469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 6) ∧
  (vasyuninBEntryFormula 1 6 ≤ ((96124712718770663781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 6 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log6 := prim_log_6_bounds
  have b_Vhk := cotangentSumVFormula_1_6_bounds
  have b_Vkh := cotangentSumVFormula_6_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [cotangentSumVFormula_1_6_lower, cotangentSumVFormula_1_6_upper] at b_Vhk
  simp only [cotangentSumVFormula_6_1_lower, cotangentSumVFormula_6_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_6_unfold :
    cotangentSumVFormula 5 6 =
      ((5/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((1/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_5_6_lower : ℚ := 148120776897660637849 / 109951162777600000000
def cotangentSumVFormula_5_6_upper : ℚ := 1184966232773477787833 / 879609302220800000000
theorem cotangentSumVFormula_5_6_bounds :
  ((cotangentSumVFormula_5_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 6 ∧
  cotangentSumVFormula 5 6 ≤ ((cotangentSumVFormula_5_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_6_unfold]
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
  rw [cotangentSumVFormula_5_6_lower, cotangentSumVFormula_5_6_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_6_5_unfold :
    cotangentSumVFormula 6 5 =
      ((1/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_6_5_lower : ℚ := -3134269962581291229457 / 3518437208883200000000
def cotangentSumVFormula_6_5_upper : ℚ := -3134269892212532208043 / 3518437208883200000000
theorem cotangentSumVFormula_6_5_bounds :
  ((cotangentSumVFormula_6_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 5 ∧
  cotangentSumVFormula 6 5 ≤ ((cotangentSumVFormula_6_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_6_5_lower, cotangentSumVFormula_6_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_56_formula_bound :
  (((114947505061838000563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 6) ∧
  (vasyuninBEntryFormula 5 6 ≤ ((114948630961745468187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 6 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log6 := prim_log_6_bounds
  have b_Vhk := cotangentSumVFormula_5_6_bounds
  have b_Vkh := cotangentSumVFormula_6_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [cotangentSumVFormula_5_6_lower, cotangentSumVFormula_5_6_upper] at b_Vhk
  simp only [cotangentSumVFormula_6_5_lower, cotangentSumVFormula_6_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_7_unfold :
    cotangentSumVFormula 1 7 =
      ((1/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_1_7_lower : ℚ := -3267942246185352841291 / 1759218604441600000000
def cotangentSumVFormula_1_7_upper : ℚ := -3267942211000966689959 / 1759218604441600000000
theorem cotangentSumVFormula_1_7_bounds :
  ((cotangentSumVFormula_1_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 7 ∧
  cotangentSumVFormula 1 7 ≤ ((cotangentSumVFormula_1_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_7_unfold]
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
  rw [cotangentSumVFormula_1_7_lower, cotangentSumVFormula_1_7_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_7_1_unfold :
    cotangentSumVFormula 7 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_7_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_7_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_7_1_bounds :
  ((cotangentSumVFormula_7_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 1 ∧
  cotangentSumVFormula 7 1 ≤ ((cotangentSumVFormula_7_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_1_unfold]
  rw [cotangentSumVFormula_7_1_lower, cotangentSumVFormula_7_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_17_formula_bound :
  (((42680357596436191547 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 7) ∧
  (vasyuninBEntryFormula 1 7 ≤ ((42680639071413464703 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 7 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_Vhk := cotangentSumVFormula_1_7_bounds
  have b_Vkh := cotangentSumVFormula_7_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [cotangentSumVFormula_1_7_lower, cotangentSumVFormula_1_7_upper] at b_Vhk
  simp only [cotangentSumVFormula_7_1_lower, cotangentSumVFormula_7_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_7_unfold :
    cotangentSumVFormula 2 7 =
      ((2/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_2_7_lower : ℚ := -269592303162212526729 / 439804651110400000000
def cotangentSumVFormula_2_7_upper : ℚ := -539184588732231587167 / 879609302220800000000
theorem cotangentSumVFormula_2_7_bounds :
  ((cotangentSumVFormula_2_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 7 ∧
  cotangentSumVFormula 2 7 ≤ ((cotangentSumVFormula_2_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_7_unfold]
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
  rw [cotangentSumVFormula_2_7_lower, cotangentSumVFormula_2_7_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_7_2_unfold :
    cotangentSumVFormula 7 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_7_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_7_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_7_2_bounds :
  ((cotangentSumVFormula_7_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 2 ∧
  cotangentSumVFormula 7 2 ≤ ((cotangentSumVFormula_7_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_7_2_lower, cotangentSumVFormula_7_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_27_formula_bound :
  (((8805956285835395543 / 35184372088832000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 7) ∧
  (vasyuninBEntryFormula 2 7 ≤ ((35224106618318589703 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 7 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_Vhk := cotangentSumVFormula_2_7_bounds
  have b_Vkh := cotangentSumVFormula_7_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [cotangentSumVFormula_2_7_lower, cotangentSumVFormula_2_7_upper] at b_Vhk
  simp only [cotangentSumVFormula_7_2_lower, cotangentSumVFormula_7_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_7_unfold :
    cotangentSumVFormula 3 7 =
      ((3/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_3_7_lower : ℚ := 154071743954285493417 / 879609302220800000000
def cotangentSumVFormula_3_7_upper : ℚ := 154071761546478569083 / 879609302220800000000
theorem cotangentSumVFormula_3_7_bounds :
  ((cotangentSumVFormula_3_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 7 ∧
  cotangentSumVFormula 3 7 ≤ ((cotangentSumVFormula_3_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_7_unfold]
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
  rw [cotangentSumVFormula_3_7_lower, cotangentSumVFormula_3_7_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_7_3_unfold :
    cotangentSumVFormula 7 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_7_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_7_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_7_3_bounds :
  ((cotangentSumVFormula_7_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 3 ∧
  cotangentSumVFormula 7 3 ≤ ((cotangentSumVFormula_7_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_7_3_lower, cotangentSumVFormula_7_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_37_formula_bound :
  (((62136949377017429969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 7) ∧
  (vasyuninBEntryFormula 3 7 ≤ ((62137512326971257531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 7 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_Vhk := cotangentSumVFormula_3_7_bounds
  have b_Vkh := cotangentSumVFormula_7_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [cotangentSumVFormula_3_7_lower, cotangentSumVFormula_3_7_upper] at b_Vhk
  simp only [cotangentSumVFormula_7_3_lower, cotangentSumVFormula_7_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_7_unfold :
    cotangentSumVFormula 4 7 =
      ((4/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_4_7_lower : ℚ := -2465148184743653589703 / 14073748835532800000000
def cotangentSumVFormula_4_7_upper : ℚ := -2465147903268565160297 / 14073748835532800000000
theorem cotangentSumVFormula_4_7_bounds :
  ((cotangentSumVFormula_4_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 7 ∧
  cotangentSumVFormula 4 7 ≤ ((cotangentSumVFormula_4_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_7_unfold]
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
  rw [cotangentSumVFormula_4_7_lower, cotangentSumVFormula_4_7_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_7_4_unfold :
    cotangentSumVFormula 7 4 =
      ((3/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((1/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_7_4_lower : ℚ := 1759218569257225176793 / 3518437208883200000000
def cotangentSumVFormula_7_4_upper : ℚ := 1759218639625974823207 / 3518437208883200000000
theorem cotangentSumVFormula_7_4_bounds :
  ((cotangentSumVFormula_7_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 4 ∧
  cotangentSumVFormula 7 4 ≤ ((cotangentSumVFormula_7_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_7_4_lower, cotangentSumVFormula_7_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_47_formula_bound :
  (((112266846424871375563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 7) ∧
  (vasyuninBEntryFormula 4 7 ≤ ((112267972324778780687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 7 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_Vhk := cotangentSumVFormula_4_7_bounds
  have b_Vkh := cotangentSumVFormula_7_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [cotangentSumVFormula_4_7_lower, cotangentSumVFormula_4_7_upper] at b_Vhk
  simp only [cotangentSumVFormula_7_4_lower, cotangentSumVFormula_7_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_7_unfold :
    cotangentSumVFormula 5 7 =
      ((5/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_5_7_lower : ℚ := 2156738354928926739293 / 3518437208883200000000
def cotangentSumVFormula_5_7_upper : ℚ := 2156738425297699041957 / 3518437208883200000000
theorem cotangentSumVFormula_5_7_bounds :
  ((cotangentSumVFormula_5_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 7 ∧
  cotangentSumVFormula 5 7 ≤ ((cotangentSumVFormula_5_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_7_unfold]
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
  rw [cotangentSumVFormula_5_7_lower, cotangentSumVFormula_5_7_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_7_5_unfold :
    cotangentSumVFormula 7 5 =
      ((2/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_7_5_lower : ℚ := -2260935825867423195031 / 28147497671065600000000
def cotangentSumVFormula_7_5_upper : ℚ := -2260935262917351804969 / 28147497671065600000000
theorem cotangentSumVFormula_7_5_bounds :
  ((cotangentSumVFormula_7_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 5 ∧
  cotangentSumVFormula 7 5 ≤ ((cotangentSumVFormula_7_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_7_5_lower, cotangentSumVFormula_7_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_57_formula_bound :
  (((51395440525268304969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 7) ∧
  (vasyuninBEntryFormula 5 7 ≤ ((12849000868805505789 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 7 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_Vhk := cotangentSumVFormula_5_7_bounds
  have b_Vkh := cotangentSumVFormula_7_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [cotangentSumVFormula_5_7_lower, cotangentSumVFormula_5_7_upper] at b_Vhk
  simp only [cotangentSumVFormula_7_5_lower, cotangentSumVFormula_7_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_6_7_unfold :
    cotangentSumVFormula 6 7 =
      ((6/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 6 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 6 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 6 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 6 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 6 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 6 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_6_7_lower : ℚ := 1633971105500482368417 / 879609302220800000000
def cotangentSumVFormula_6_7_upper : ℚ := 1633971123092677006583 / 879609302220800000000
theorem cotangentSumVFormula_6_7_bounds :
  ((cotangentSumVFormula_6_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 6 7 ∧
  cotangentSumVFormula 6 7 ≤ ((cotangentSumVFormula_6_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_6_7_unfold]
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
  rw [cotangentSumVFormula_6_7_lower, cotangentSumVFormula_6_7_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_7_6_unfold :
    cotangentSumVFormula 7 6 =
      ((1/6 : ℚ) : ℝ) * cotangentTermV 1 6    + 
      ((2/6 : ℚ) : ℝ) * cotangentTermV 2 6    + 
      ((3/6 : ℚ) : ℝ) * cotangentTermV 3 6    + 
      ((4/6 : ℚ) : ℝ) * cotangentTermV 4 6    + 
      ((5/6 : ℚ) : ℝ) * cotangentTermV 5 6 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_6]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((1/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((2/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((3/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((4/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((6 : ℕ) : ℝ)) = ((5/6 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5]
  try ring

def cotangentSumVFormula_7_6_lower : ℚ := -2369932465546953622541 / 1759218604441600000000
def cotangentSumVFormula_7_6_upper : ℚ := -2369932430362564346209 / 1759218604441600000000
theorem cotangentSumVFormula_7_6_bounds :
  ((cotangentSumVFormula_7_6_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 6 ∧
  cotangentSumVFormula 7 6 ≤ ((cotangentSumVFormula_7_6_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_6_unfold]
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
  rw [cotangentSumVFormula_7_6_lower, cotangentSumVFormula_7_6_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_67_formula_bound :
  (((98051860726605188063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 6 7) ∧
  (vasyuninBEntryFormula 6 7 ≤ ((98052986626512718187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 6 7 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log6 := prim_log_6_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_Vhk := cotangentSumVFormula_6_7_bounds
  have b_Vkh := cotangentSumVFormula_7_6_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_6_lower, prim_log_6_upper] at b_log6
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [cotangentSumVFormula_6_7_lower, cotangentSumVFormula_6_7_upper] at b_Vhk
  simp only [cotangentSumVFormula_7_6_lower, cotangentSumVFormula_7_6_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_8_unfold :
    cotangentSumVFormula 1 8 =
      ((1/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_1_8_lower : ℚ := -530891178951771302427 / 219902325555200000000
def cotangentSumVFormula_1_8_upper : ℚ := -1061782349107446067021 / 439804651110400000000
theorem cotangentSumVFormula_1_8_bounds :
  ((cotangentSumVFormula_1_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 8 ∧
  cotangentSumVFormula 1 8 ≤ ((cotangentSumVFormula_1_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_8_unfold]
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
  rw [cotangentSumVFormula_1_8_lower, cotangentSumVFormula_1_8_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_8_1_unfold :
    cotangentSumVFormula 8 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_8_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_8_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_8_1_bounds :
  ((cotangentSumVFormula_8_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 1 ∧
  cotangentSumVFormula 8 1 ≤ ((cotangentSumVFormula_8_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_1_unfold]
  rw [cotangentSumVFormula_8_1_lower, cotangentSumVFormula_8_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_18_formula_bound :
  (((4809617257838314959 / 17592186044416000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 8) ∧
  (vasyuninBEntryFormula 1 8 ≤ ((19238609768841849539 / 70368744177664000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 8 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log8 := prim_log_8_bounds
  have b_Vhk := cotangentSumVFormula_1_8_bounds
  have b_Vkh := cotangentSumVFormula_8_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [cotangentSumVFormula_1_8_lower, cotangentSumVFormula_1_8_upper] at b_Vhk
  simp only [cotangentSumVFormula_8_1_lower, cotangentSumVFormula_8_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_8_unfold :
    cotangentSumVFormula 3 8 =
      ((3/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_3_8_lower : ℚ := -728692222730972372541 / 1759218604441600000000
def cotangentSumVFormula_3_8_upper : ℚ := -728692187546586221209 / 1759218604441600000000
theorem cotangentSumVFormula_3_8_bounds :
  ((cotangentSumVFormula_3_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 8 ∧
  cotangentSumVFormula 3 8 ≤ ((cotangentSumVFormula_3_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_8_unfold]
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
  rw [cotangentSumVFormula_3_8_lower, cotangentSumVFormula_3_8_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_8_3_unfold :
    cotangentSumVFormula 8 3 =
      ((2/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((1/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_8_3_lower : ℚ := 338561760687064346209 / 1759218604441600000000
def cotangentSumVFormula_8_3_upper : ℚ := 169280897935719975333 / 879609302220800000000
theorem cotangentSumVFormula_8_3_bounds :
  ((cotangentSumVFormula_8_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 3 ∧
  cotangentSumVFormula 8 3 ≤ ((cotangentSumVFormula_8_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_8_3_lower, cotangentSumVFormula_8_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_38_formula_bound :
  (((113290999985669031813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 8) ∧
  (vasyuninBEntryFormula 3 8 ≤ ((113292125885576593187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 8 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log8 := prim_log_8_bounds
  have b_Vhk := cotangentSumVFormula_3_8_bounds
  have b_Vkh := cotangentSumVFormula_8_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [cotangentSumVFormula_3_8_lower, cotangentSumVFormula_3_8_upper] at b_Vhk
  simp only [cotangentSumVFormula_8_3_lower, cotangentSumVFormula_8_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_8_unfold :
    cotangentSumVFormula 5 8 =
      ((5/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_5_8_lower : ℚ := 728692187546585439959 / 1759218604441600000000
def cotangentSumVFormula_5_8_upper : ℚ := 728692222730973935041 / 1759218604441600000000
theorem cotangentSumVFormula_5_8_bounds :
  ((cotangentSumVFormula_5_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 8 ∧
  cotangentSumVFormula 5 8 ≤ ((cotangentSumVFormula_5_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_8_unfold]
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
  rw [cotangentSumVFormula_5_8_lower, cotangentSumVFormula_5_8_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_8_5_unfold :
    cotangentSumVFormula 8 5 =
      ((3/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((4/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_8_5_lower : ℚ := 2260935262917356492469 / 28147497671065600000000
def cotangentSumVFormula_8_5_upper : ℚ := 2260935825867424757531 / 28147497671065600000000
theorem cotangentSumVFormula_8_5_bounds :
  ((cotangentSumVFormula_8_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 5 ∧
  cotangentSumVFormula 8 5 ≤ ((cotangentSumVFormula_8_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_8_5_lower, cotangentSumVFormula_8_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_58_formula_bound :
  (((2952160128819627459 / 17592186044416000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 8) ∧
  (vasyuninBEntryFormula 5 8 ≤ ((23617562505533870953 / 140737488355328000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 8 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log8 := prim_log_8_bounds
  have b_Vhk := cotangentSumVFormula_5_8_bounds
  have b_Vkh := cotangentSumVFormula_8_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [cotangentSumVFormula_5_8_lower, cotangentSumVFormula_5_8_upper] at b_Vhk
  simp only [cotangentSumVFormula_8_5_lower, cotangentSumVFormula_8_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_8_unfold :
    cotangentSumVFormula 7 8 =
      ((7/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((1/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_7_8_lower : ℚ := 2123564698214891743417 / 879609302220800000000
def cotangentSumVFormula_7_8_upper : ℚ := 2123564715807086381583 / 879609302220800000000
theorem cotangentSumVFormula_7_8_bounds :
  ((cotangentSumVFormula_7_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 8 ∧
  cotangentSumVFormula 7 8 ≤ ((cotangentSumVFormula_7_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_8_unfold]
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
  rw [cotangentSumVFormula_7_8_lower, cotangentSumVFormula_7_8_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_8_7_unfold :
    cotangentSumVFormula 8 7 =
      ((1/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_8_7_lower : ℚ := -3267942246185352841291 / 1759218604441600000000
def cotangentSumVFormula_8_7_upper : ℚ := -3267942211000966689959 / 1759218604441600000000
theorem cotangentSumVFormula_8_7_bounds :
  ((cotangentSumVFormula_8_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 7 ∧
  cotangentSumVFormula 8 7 ≤ ((cotangentSumVFormula_8_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_7_unfold]
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
  rw [cotangentSumVFormula_8_7_lower, cotangentSumVFormula_8_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_78_formula_bound :
  (((42793385229444554969 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 8) ∧
  (vasyuninBEntryFormula 7 8 ≤ ((42793948179398226281 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 8 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log8 := prim_log_8_bounds
  have b_Vhk := cotangentSumVFormula_7_8_bounds
  have b_Vkh := cotangentSumVFormula_8_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [cotangentSumVFormula_7_8_lower, cotangentSumVFormula_7_8_upper] at b_Vhk
  simp only [cotangentSumVFormula_8_7_lower, cotangentSumVFormula_8_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_9_unfold :
    cotangentSumVFormula 1 9 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_1_9_lower : ℚ := -1324275640802612526729 / 439804651110400000000
def cotangentSumVFormula_1_9_upper : ℚ := -82767227000406858681 / 27487790694400000000
theorem cotangentSumVFormula_1_9_bounds :
  ((cotangentSumVFormula_1_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 9 ∧
  cotangentSumVFormula 1 9 ≤ ((cotangentSumVFormula_1_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_9_unfold]
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
  rw [cotangentSumVFormula_1_9_lower, cotangentSumVFormula_1_9_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_9_1_unfold :
    cotangentSumVFormula 9 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_9_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_9_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_9_1_bounds :
  ((cotangentSumVFormula_9_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 1 ∧
  cotangentSumVFormula 9 1 ≤ ((cotangentSumVFormula_9_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_1_unfold]
  rw [cotangentSumVFormula_9_1_lower, cotangentSumVFormula_9_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_19_formula_bound :
  (((70185865371920648719 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 9) ∧
  (vasyuninBEntryFormula 1 9 ≤ ((70186428321875913781 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 9 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log9 := prim_log_9_bounds
  have b_Vhk := cotangentSumVFormula_1_9_bounds
  have b_Vkh := cotangentSumVFormula_9_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [cotangentSumVFormula_1_9_lower, cotangentSumVFormula_1_9_upper] at b_Vhk
  simp only [cotangentSumVFormula_9_1_lower, cotangentSumVFormula_9_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_2_9_unfold :
    cotangentSumVFormula 2 9 =
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
  have hf_1 : Int.fract (((1 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 2 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_2_9_lower : ℚ := -1169176792736990287833 / 879609302220800000000
def cotangentSumVFormula_2_9_upper : ℚ := -1169176775144784712167 / 879609302220800000000
theorem cotangentSumVFormula_2_9_bounds :
  ((cotangentSumVFormula_2_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 2 9 ∧
  cotangentSumVFormula 2 9 ≤ ((cotangentSumVFormula_2_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_2_9_unfold]
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
  rw [cotangentSumVFormula_2_9_lower, cotangentSumVFormula_2_9_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_9_2_unfold :
    cotangentSumVFormula 9 2 =
      ((1/2 : ℚ) : ℝ) * cotangentTermV 1 2 := by
  unfold cotangentSumVFormula
  rw [Finset.sum_Ico_succ_top (by decide)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = ((1/2 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1]
  try ring

def cotangentSumVFormula_9_2_lower : ℚ := -75557863916583130059761 / 7555786372591432341913600000000
def cotangentSumVFormula_9_2_upper : ℚ := 75557864379021532403511 / 7555786372591432341913600000000
theorem cotangentSumVFormula_9_2_bounds :
  ((cotangentSumVFormula_9_2_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 2 ∧
  cotangentSumVFormula 9 2 ≤ ((cotangentSumVFormula_9_2_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_2_unfold]
  have b_cot_1 := cot_pi_1_2_bounds
  simp only [cot_pi_1_2_lower, cot_pi_1_2_upper] at b_cot_1
  rw [cotangentSumVFormula_9_2_lower, cotangentSumVFormula_9_2_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_29_formula_bound :
  (((29377007537231660297 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 2 9) ∧
  (vasyuninBEntryFormula 2 9 ≤ ((7344322253052198207 / 35184372088832000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 2 9 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log2 : ((log_2_lower : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log_2_upper : ℚ) : ℝ) := log_2_certified_bounds
  have b_log9 := prim_log_9_bounds
  have b_Vhk := cotangentSumVFormula_2_9_bounds
  have b_Vkh := cotangentSumVFormula_9_2_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_2_lower, log_2_upper] at b_log2
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [cotangentSumVFormula_2_9_lower, cotangentSumVFormula_2_9_upper] at b_Vhk
  simp only [cotangentSumVFormula_9_2_lower, cotangentSumVFormula_9_2_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_4_9_unfold :
    cotangentSumVFormula 4 9 =
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
  have hf_1 : Int.fract (((1 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 4 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_4_9_lower : ℚ := 927378290468754971209 / 1759218604441600000000
def cotangentSumVFormula_4_9_upper : ℚ := 927378325653165341291 / 1759218604441600000000
theorem cotangentSumVFormula_4_9_bounds :
  ((cotangentSumVFormula_4_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 4 9 ∧
  cotangentSumVFormula 4 9 ≤ ((cotangentSumVFormula_4_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_4_9_unfold]
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
  rw [cotangentSumVFormula_4_9_lower, cotangentSumVFormula_4_9_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_9_4_unfold :
    cotangentSumVFormula 9 4 =
      ((1/4 : ℚ) : ℝ) * cotangentTermV 1 4    + 
      ((2/4 : ℚ) : ℝ) * cotangentTermV 2 4    + 
      ((3/4 : ℚ) : ℝ) * cotangentTermV 3 4 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_4]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((1/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((2/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = ((3/4 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3]
  try ring

def cotangentSumVFormula_9_4_lower : ℚ := -1759218639625974041957 / 3518437208883200000000
def cotangentSumVFormula_9_4_upper : ℚ := -1759218569257223614293 / 3518437208883200000000
theorem cotangentSumVFormula_9_4_bounds :
  ((cotangentSumVFormula_9_4_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 4 ∧
  cotangentSumVFormula 9 4 ≤ ((cotangentSumVFormula_9_4_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_4_unfold]
  have b_cot_1 := cot_pi_1_4_bounds
  simp only [cot_pi_1_4_lower, cot_pi_1_4_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_4_bounds
  simp only [cot_pi_2_4_lower, cot_pi_2_4_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_4_bounds
  simp only [cot_pi_3_4_lower, cot_pi_3_4_upper] at b_cot_3
  rw [cotangentSumVFormula_9_4_lower, cotangentSumVFormula_9_4_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_49_formula_bound :
  (((95768497114342750563 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 4 9) ∧
  (vasyuninBEntryFormula 4 9 ≤ ((95769623014250436937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 4 9 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log4 := prim_log_4_bounds
  have b_log9 := prim_log_9_bounds
  have b_Vhk := cotangentSumVFormula_4_9_bounds
  have b_Vkh := cotangentSumVFormula_9_4_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_4_lower, prim_log_4_upper] at b_log4
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [cotangentSumVFormula_4_9_lower, cotangentSumVFormula_4_9_upper] at b_Vhk
  simp only [cotangentSumVFormula_9_4_lower, cotangentSumVFormula_9_4_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_5_9_unfold :
    cotangentSumVFormula 5 9 =
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
  have hf_1 : Int.fract (((1 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 5 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_5_9_lower : ℚ := -927378325653162216291 / 1759218604441600000000
def cotangentSumVFormula_5_9_upper : ℚ := -927378290468754971209 / 1759218604441600000000
theorem cotangentSumVFormula_5_9_bounds :
  ((cotangentSumVFormula_5_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 5 9 ∧
  cotangentSumVFormula 5 9 ≤ ((cotangentSumVFormula_5_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_5_9_unfold]
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
  rw [cotangentSumVFormula_5_9_lower, cotangentSumVFormula_5_9_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_9_5_unfold :
    cotangentSumVFormula 9 5 =
      ((4/5 : ℚ) : ℝ) * cotangentTermV 1 5    + 
      ((3/5 : ℚ) : ℝ) * cotangentTermV 2 5    + 
      ((2/5 : ℚ) : ℝ) * cotangentTermV 3 5    + 
      ((1/5 : ℚ) : ℝ) * cotangentTermV 4 5 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_5]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((4/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((3/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((2/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = ((1/5 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4]
  try ring

def cotangentSumVFormula_9_5_lower : ℚ := 3134269892212533770543 / 3518437208883200000000
def cotangentSumVFormula_9_5_upper : ℚ := 3134269962581292010707 / 3518437208883200000000
theorem cotangentSumVFormula_9_5_bounds :
  ((cotangentSumVFormula_9_5_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 5 ∧
  cotangentSumVFormula 9 5 ≤ ((cotangentSumVFormula_9_5_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_5_unfold]
  have b_cot_1 := cot_pi_1_5_bounds
  simp only [cot_pi_1_5_lower, cot_pi_1_5_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_5_bounds
  simp only [cot_pi_2_5_lower, cot_pi_2_5_upper] at b_cot_2
  have b_cot_3 := cot_pi_3_5_bounds
  simp only [cot_pi_3_5_lower, cot_pi_3_5_upper] at b_cot_3
  have b_cot_4 := cot_pi_4_5_bounds
  simp only [cot_pi_4_5_lower, cot_pi_4_5_upper] at b_cot_4
  rw [cotangentSumVFormula_9_5_lower, cotangentSumVFormula_9_5_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_59_formula_bound :
  (((44271487636641961219 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 5 9) ∧
  (vasyuninBEntryFormula 5 9 ≤ ((44272050586595757531 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 5 9 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log5 : ((log_5_lower : ℚ) : ℝ) ≤ Real.log 5 ∧ Real.log 5 ≤ ((log_5_upper : ℚ) : ℝ) := log_5_certified_bounds
  have b_log9 := prim_log_9_bounds
  have b_Vhk := cotangentSumVFormula_5_9_bounds
  have b_Vkh := cotangentSumVFormula_9_5_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_5_lower, log_5_upper] at b_log5
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [cotangentSumVFormula_5_9_lower, cotangentSumVFormula_5_9_upper] at b_Vhk
  simp only [cotangentSumVFormula_9_5_lower, cotangentSumVFormula_9_5_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_9_unfold :
    cotangentSumVFormula 7 9 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_7_9_lower : ℚ := 584588387572393723271 / 439804651110400000000
def cotangentSumVFormula_7_9_upper : ℚ := 1169176792736990287833 / 879609302220800000000
theorem cotangentSumVFormula_7_9_bounds :
  ((cotangentSumVFormula_7_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 9 ∧
  cotangentSumVFormula 7 9 ≤ ((cotangentSumVFormula_7_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_9_unfold]
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
  rw [cotangentSumVFormula_7_9_lower, cotangentSumVFormula_7_9_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_9_7_unfold :
    cotangentSumVFormula 9 7 =
      ((2/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((3/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_9_7_lower : ℚ := -269592303162212526729 / 439804651110400000000
def cotangentSumVFormula_9_7_upper : ℚ := -539184588732231587167 / 879609302220800000000
theorem cotangentSumVFormula_9_7_bounds :
  ((cotangentSumVFormula_9_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 7 ∧
  cotangentSumVFormula 9 7 ≤ ((cotangentSumVFormula_9_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_7_unfold]
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
  rw [cotangentSumVFormula_9_7_lower, cotangentSumVFormula_9_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_79_formula_bound :
  (((38910032401906117469 / 281474976710656000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 9) ∧
  (vasyuninBEntryFormula 7 9 ≤ ((4863824418982479457 / 35184372088832000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 9 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log9 := prim_log_9_bounds
  have b_Vhk := cotangentSumVFormula_7_9_bounds
  have b_Vkh := cotangentSumVFormula_9_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [cotangentSumVFormula_7_9_lower, cotangentSumVFormula_7_9_upper] at b_Vhk
  simp only [cotangentSumVFormula_9_7_lower, cotangentSumVFormula_9_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_8_9_unfold :
    cotangentSumVFormula 8 9 =
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
  have hf_1 : Int.fract (((1 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 8 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_8_9_lower : ℚ := 1324275632006511692021 / 439804651110400000000
def cotangentSumVFormula_8_9_upper : ℚ := 165534455100326517013 / 54975581388800000000
theorem cotangentSumVFormula_8_9_bounds :
  ((cotangentSumVFormula_8_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 8 9 ∧
  cotangentSumVFormula 8 9 ≤ ((cotangentSumVFormula_8_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_8_9_unfold]
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
  rw [cotangentSumVFormula_8_9_lower, cotangentSumVFormula_8_9_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_9_8_unfold :
    cotangentSumVFormula 9 8 =
      ((1/8 : ℚ) : ℝ) * cotangentTermV 1 8    + 
      ((2/8 : ℚ) : ℝ) * cotangentTermV 2 8    + 
      ((3/8 : ℚ) : ℝ) * cotangentTermV 3 8    + 
      ((4/8 : ℚ) : ℝ) * cotangentTermV 4 8    + 
      ((5/8 : ℚ) : ℝ) * cotangentTermV 5 8    + 
      ((6/8 : ℚ) : ℝ) * cotangentTermV 6 8    + 
      ((7/8 : ℚ) : ℝ) * cotangentTermV 7 8 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_8]
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((1/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((2/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((3/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((4/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((5/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((6/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((8 : ℕ) : ℝ)) = ((7/8 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7]
  try ring

def cotangentSumVFormula_9_8_lower : ℚ := -530891178951771302427 / 219902325555200000000
def cotangentSumVFormula_9_8_upper : ℚ := -1061782349107446067021 / 439804651110400000000
theorem cotangentSumVFormula_9_8_bounds :
  ((cotangentSumVFormula_9_8_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 8 ∧
  cotangentSumVFormula 9 8 ≤ ((cotangentSumVFormula_9_8_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_8_unfold]
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
  rw [cotangentSumVFormula_9_8_lower, cotangentSumVFormula_9_8_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_89_formula_bound :
  (((75991545650209813063 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 8 9) ∧
  (vasyuninBEntryFormula 8 9 ≤ ((75992671550117155687 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 8 9 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log8 := prim_log_8_bounds
  have b_log9 := prim_log_9_bounds
  have b_Vhk := cotangentSumVFormula_8_9_bounds
  have b_Vkh := cotangentSumVFormula_9_8_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_8_lower, prim_log_8_upper] at b_log8
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [cotangentSumVFormula_8_9_lower, cotangentSumVFormula_8_9_upper] at b_Vhk
  simp only [cotangentSumVFormula_9_8_lower, cotangentSumVFormula_9_8_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_1_10_unfold :
    cotangentSumVFormula 1 10 =
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
  have hf_1 : Int.fract (((1 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 1 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_1_10_lower : ℚ := -1602462085977636745479 / 439804651110400000000
def cotangentSumVFormula_1_10_upper : ℚ := -801231038590768541323 / 219902325555200000000
theorem cotangentSumVFormula_1_10_bounds :
  ((cotangentSumVFormula_1_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 1 10 ∧
  cotangentSumVFormula 1 10 ≤ ((cotangentSumVFormula_1_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_1_10_unfold]
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
  rw [cotangentSumVFormula_1_10_lower, cotangentSumVFormula_1_10_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_10_1_unfold :
    cotangentSumVFormula 10 1 =
0 := by
  unfold cotangentSumVFormula
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  try ring

def cotangentSumVFormula_10_1_lower : ℚ := -1 / 100000000
def cotangentSumVFormula_10_1_upper : ℚ := 1 / 100000000
theorem cotangentSumVFormula_10_1_bounds :
  ((cotangentSumVFormula_10_1_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 1 ∧
  cotangentSumVFormula 10 1 ≤ ((cotangentSumVFormula_10_1_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_1_unfold]
  rw [cotangentSumVFormula_10_1_lower, cotangentSumVFormula_10_1_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_110_formula_bound :
  (((129214581261485531813 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 1 10) ∧
  (vasyuninBEntryFormula 1 10 ≤ ((129215707161395218187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 1 10 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log1 : (0 : ℝ) ≤ Real.log 1 ∧ Real.log 1 ≤ 0 := by simp
  have b_log10 := prim_log_10_bounds
  have b_Vhk := cotangentSumVFormula_1_10_bounds
  have b_Vkh := cotangentSumVFormula_10_1_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [cotangentSumVFormula_1_10_lower, cotangentSumVFormula_1_10_upper] at b_Vhk
  simp only [cotangentSumVFormula_10_1_lower, cotangentSumVFormula_10_1_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_3_10_unfold :
    cotangentSumVFormula 3 10 =
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
  have hf_1 : Int.fract (((1 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 3 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_3_10_lower : ℚ := -2003802190385119354457 / 3518437208883200000000
def cotangentSumVFormula_3_10_upper : ℚ := -2003802120016316583043 / 3518437208883200000000
theorem cotangentSumVFormula_3_10_bounds :
  ((cotangentSumVFormula_3_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 3 10 ∧
  cotangentSumVFormula 3 10 ≤ ((cotangentSumVFormula_3_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_3_10_unfold]
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
  rw [cotangentSumVFormula_3_10_lower, cotangentSumVFormula_3_10_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_10_3_unfold :
    cotangentSumVFormula 10 3 =
      ((1/3 : ℚ) : ℝ) * cotangentTermV 1 3    + 
      ((2/3 : ℚ) : ℝ) * cotangentTermV 2 3 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_3]
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((1/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((3 : ℕ) : ℝ)) = ((2/3 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2]
  try ring

def cotangentSumVFormula_10_3_lower : ℚ := -1354247183485757068289 / 7036874417766400000000
def cotangentSumVFormula_10_3_upper : ℚ := -1354247042748253087961 / 7036874417766400000000
theorem cotangentSumVFormula_10_3_bounds :
  ((cotangentSumVFormula_10_3_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 3 ∧
  cotangentSumVFormula 10 3 ≤ ((cotangentSumVFormula_10_3_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_3_unfold]
  have b_cot_1 := cot_pi_1_3_bounds
  simp only [cot_pi_1_3_lower, cot_pi_1_3_upper] at b_cot_1
  have b_cot_2 := cot_pi_2_3_bounds
  simp only [cot_pi_2_3_lower, cot_pi_2_3_upper] at b_cot_2
  rw [cotangentSumVFormula_10_3_lower, cotangentSumVFormula_10_3_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_310_formula_bound :
  (((97151200531643594313 / 562949953421312000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 3 10) ∧
  (vasyuninBEntryFormula 3 10 ≤ ((97152326431551436937 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 3 10 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log3 : ((log_3_lower : ℚ) : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ ((log_3_upper : ℚ) : ℝ) := log_3_certified_bounds
  have b_log10 := prim_log_10_bounds
  have b_Vhk := cotangentSumVFormula_3_10_bounds
  have b_Vkh := cotangentSumVFormula_10_3_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_3_lower, log_3_upper] at b_log3
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [cotangentSumVFormula_3_10_lower, cotangentSumVFormula_3_10_upper] at b_Vhk
  simp only [cotangentSumVFormula_10_3_lower, cotangentSumVFormula_10_3_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_7_10_unfold :
    cotangentSumVFormula 7 10 =
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
  have hf_1 : Int.fract (((1 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 7 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_7_10_lower : ℚ := 2003802120016315801793 / 3518437208883200000000
def cotangentSumVFormula_7_10_upper : ℚ := 2003802190385117791957 / 3518437208883200000000
theorem cotangentSumVFormula_7_10_bounds :
  ((cotangentSumVFormula_7_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 7 10 ∧
  cotangentSumVFormula 7 10 ≤ ((cotangentSumVFormula_7_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_7_10_unfold]
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
  rw [cotangentSumVFormula_7_10_lower, cotangentSumVFormula_7_10_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_10_7_unfold :
    cotangentSumVFormula 10 7 =
      ((3/7 : ℚ) : ℝ) * cotangentTermV 1 7    + 
      ((6/7 : ℚ) : ℝ) * cotangentTermV 2 7    + 
      ((2/7 : ℚ) : ℝ) * cotangentTermV 3 7    + 
      ((5/7 : ℚ) : ℝ) * cotangentTermV 4 7    + 
      ((1/7 : ℚ) : ℝ) * cotangentTermV 5 7    + 
      ((4/7 : ℚ) : ℝ) * cotangentTermV 6 7 := by
  unfold cotangentSumVFormula
  rw [sum_Ico_1_7]
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((3/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((6/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((2/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((5/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((1/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((7 : ℕ) : ℝ)) = ((4/7 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6]
  try ring

def cotangentSumVFormula_10_7_lower : ℚ := 154071743954285493417 / 879609302220800000000
def cotangentSumVFormula_10_7_upper : ℚ := 154071761546478569083 / 879609302220800000000
theorem cotangentSumVFormula_10_7_bounds :
  ((cotangentSumVFormula_10_7_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 7 ∧
  cotangentSumVFormula 10 7 ≤ ((cotangentSumVFormula_10_7_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_7_unfold]
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
  rw [cotangentSumVFormula_10_7_lower, cotangentSumVFormula_10_7_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_710_formula_bound :
  (((18116550019589441547 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 7 10) ∧
  (vasyuninBEntryFormula 7 10 ≤ ((36233662989132570031 / 281474976710656000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 7 10 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log7 : ((log_7_lower : ℚ) : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ ((log_7_upper : ℚ) : ℝ) := log_7_certified_bounds
  have b_log10 := prim_log_10_bounds
  have b_Vhk := cotangentSumVFormula_7_10_bounds
  have b_Vkh := cotangentSumVFormula_10_7_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [log_7_lower, log_7_upper] at b_log7
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [cotangentSumVFormula_7_10_lower, cotangentSumVFormula_7_10_upper] at b_Vhk
  simp only [cotangentSumVFormula_10_7_lower, cotangentSumVFormula_10_7_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

theorem cotangentSumVFormula_9_10_unfold :
    cotangentSumVFormula 9 10 =
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
  have hf_1 : Int.fract (((1 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((9/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((8/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((7/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((6/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((5/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((4/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((3/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((2/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_9 : Int.fract (((9 * 9 : ℕ) : ℝ) / ((10 : ℕ) : ℝ)) = ((1/10 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8, hf_9]
  try ring

def cotangentSumVFormula_9_10_lower : ℚ := 3204924154363070649667 / 879609302220800000000
def cotangentSumVFormula_9_10_upper : ℚ := 3204924171955274662833 / 879609302220800000000
theorem cotangentSumVFormula_9_10_bounds :
  ((cotangentSumVFormula_9_10_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 9 10 ∧
  cotangentSumVFormula 9 10 ≤ ((cotangentSumVFormula_9_10_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_9_10_unfold]
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
  rw [cotangentSumVFormula_9_10_lower, cotangentSumVFormula_9_10_upper]
  constructor
  · linarith
  · linarith

theorem cotangentSumVFormula_10_9_unfold :
    cotangentSumVFormula 10 9 =
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
  have hf_1 : Int.fract (((1 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((1/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_2 : Int.fract (((2 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((2/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_3 : Int.fract (((3 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((3/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_4 : Int.fract (((4 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((4/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_5 : Int.fract (((5 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((5/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_6 : Int.fract (((6 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((6/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_7 : Int.fract (((7 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((7/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  have hf_8 : Int.fract (((8 * 10 : ℕ) : ℝ) / ((9 : ℕ) : ℝ)) = ((8/9 : ℚ) : ℝ) := by norm_num [Int.fract]
  simp only [hf_1, hf_2, hf_3, hf_4, hf_5, hf_6, hf_7, hf_8]
  try ring

def cotangentSumVFormula_10_9_lower : ℚ := -1324275640802612526729 / 439804651110400000000
def cotangentSumVFormula_10_9_upper : ℚ := -82767227000406858681 / 27487790694400000000
theorem cotangentSumVFormula_10_9_bounds :
  ((cotangentSumVFormula_10_9_lower : ℚ) : ℝ) ≤ cotangentSumVFormula 10 9 ∧
  cotangentSumVFormula 10 9 ≤ ((cotangentSumVFormula_10_9_upper : ℚ) : ℝ) := by
  rw [cotangentSumVFormula_10_9_unfold]
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
  rw [cotangentSumVFormula_10_9_lower, cotangentSumVFormula_10_9_upper]
  constructor
  · linarith
  · linarith

theorem vasyuninBEntry_910_formula_bound :
  (((17091705790496472797 / 140737488355328000000 : ℚ) : ℝ) ≤ vasyuninBEntryFormula 9 10) ∧
  (vasyuninBEntryFormula 9 10 ≤ ((68367949061893343187 / 562949953421312000000 : ℚ) : ℝ)) := by
  unfold vasyuninBEntryFormula
  rw [vasyunin_log_div 9 10 (by norm_num) (by norm_num)]
  have b_log2pi := log_two_pi_certified_bounds
  have b_gamma := euler_gamma_certified_bounds
  have b_pi := prim_pi_bounds
  have b_log9 := prim_log_9_bounds
  have b_log10 := prim_log_10_bounds
  have b_Vhk := cotangentSumVFormula_9_10_bounds
  have b_Vkh := cotangentSumVFormula_10_9_bounds
  -- apply definitions of bounds for nlinarith
  simp only [log_two_pi_lower, log_two_pi_upper] at b_log2pi
  simp only [euler_gamma_lower, euler_gamma_upper] at b_gamma
  simp only [prim_pi_lower, prim_pi_upper] at b_pi
  simp only [prim_log_9_lower, prim_log_9_upper] at b_log9
  simp only [prim_log_10_lower, prim_log_10_upper] at b_log10
  simp only [cotangentSumVFormula_9_10_lower, cotangentSumVFormula_9_10_upper] at b_Vhk
  simp only [cotangentSumVFormula_10_9_lower, cotangentSumVFormula_10_9_upper] at b_Vkh
  push_cast at *
  constructor
  · nlinarith
  · nlinarith

end RH.Certificates.Generated
