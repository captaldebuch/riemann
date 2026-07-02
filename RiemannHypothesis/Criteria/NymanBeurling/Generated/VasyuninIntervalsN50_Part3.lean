import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part1
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part2

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G10_7_formula : baezDuarteGramEntry 10 7 = vasyuninBEntry 7 10 := by
  rw [baezDuarteGramEntry_symm 10 7]
  exact G7_10_formula

theorem G10_7_interval :
    ((((86672617/673830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 7) ∧
    (baezDuarteGramEntry 10 7 ≤ (((86807383/673830000) : ℚ) : ℝ)) := by
  rw [G10_7_formula]
  exact vasyuninBEntry_7_10_eval

def interval_10_7 : NamedVasyuninInterval :=
{
  h := 10
  k := 7
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_7_interval
}

theorem G10_8_formula : baezDuarteGramEntry 10 8 = vasyuninBEntry 8 10 := by
  rw [baezDuarteGramEntry_symm 10 8]
  exact G8_10_formula

theorem G10_8_interval :
    ((((12715961/102890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 8) ∧
    (baezDuarteGramEntry 10 8 ≤ (((12736539/102890000) : ℚ) : ℝ)) := by
  rw [G10_8_formula]
  exact vasyuninBEntry_8_10_eval

def interval_10_8 : NamedVasyuninInterval :=
{
  h := 10
  k := 8
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_8_interval
}

theorem G10_9_formula : baezDuarteGramEntry 10 9 = vasyuninBEntry 9 10 := by
  rw [baezDuarteGramEntry_symm 10 9]
  exact G9_10_formula

theorem G10_9_interval :
    ((((116434047/959530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 9) ∧
    (baezDuarteGramEntry 10 9 ≤ (((116625953/959530000) : ℚ) : ℝ)) := by
  rw [G10_9_formula]
  exact vasyuninBEntry_9_10_eval

def interval_10_9 : NamedVasyuninInterval :=
{
  h := 10
  k := 9
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_9_interval
}

theorem G10_10_formula_eq : baezDuarteGramEntry 10 10 = (1 / (10 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 10 := by norm_num
  rw [baez_duarte_diagonal_scaling 10 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G10_10_log_gamma_interval :
  ((((39728461/315390000) : ℚ) : ℝ) ≤ (1 / (10 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (10 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((39791539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 10 (by norm_num)
  constructor
  · have : ((((39728461/315390000) : ℚ) : ℝ) ≤ (1 / (10 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (10 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((39791539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G10_10_interval : ((((39728461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 10) ∧ (baezDuarteGramEntry 10 10 ≤ (((39791539/315390000) : ℚ) : ℝ)) := by
  rw [G10_10_formula_eq]
  exact G10_10_log_gamma_interval

def interval_10_10 : NamedVasyuninInterval :=
{
  h := 10
  k := 10
  lower := (39728461/315390000)
  upper := (39791539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G10_10_interval
}

theorem G10_11_formula : baezDuarteGramEntry 10 11 = vasyuninBEntry 10 11 := vasyuninBEntry_correct_axiom 10 11

theorem vasyuninBEntry_10_11_eval :
    ((((79467961/720390000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 11) ∧
    (vasyuninBEntry 10 11 ≤ (((79612039/720390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1011_formula_bound
  constructor <;> linarith

theorem G10_11_interval :
    ((((79467961/720390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 11) ∧
    (baezDuarteGramEntry 10 11 ≤ (((79612039/720390000) : ℚ) : ℝ)) := by
  rw [G10_11_formula]
  exact vasyuninBEntry_10_11_eval

def interval_10_11 : NamedVasyuninInterval :=
{
  h := 10
  k := 11
  lower := (79467961/720390000)
  upper := (79612039/720390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_11_interval
}

theorem G10_12_formula : baezDuarteGramEntry 10 12 = vasyuninBEntry 10 12 := vasyuninBEntry_correct_axiom 10 12

theorem vasyuninBEntry_10_12_eval :
    ((((17482859/171410000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 12) ∧
    (vasyuninBEntry 10 12 ≤ (((17517141/171410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_12_interval :
    ((((17482859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 12) ∧
    (baezDuarteGramEntry 10 12 ≤ (((17517141/171410000) : ℚ) : ℝ)) := by
  rw [G10_12_formula]
  exact vasyuninBEntry_10_12_eval

def interval_10_12 : NamedVasyuninInterval :=
{
  h := 10
  k := 12
  lower := (17482859/171410000)
  upper := (17517141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_12_interval
}

theorem G10_13_formula : baezDuarteGramEntry 10 13 = vasyuninBEntry 10 13 := vasyuninBEntry_correct_axiom 10 13

theorem vasyuninBEntry_10_13_eval :
    ((((22993523/239770000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 13) ∧
    (vasyuninBEntry 10 13 ≤ (((23041477/239770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1013_formula_bound
  constructor <;> linarith

theorem G10_13_interval :
    ((((22993523/239770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 13) ∧
    (baezDuarteGramEntry 10 13 ≤ (((23041477/239770000) : ℚ) : ℝ)) := by
  rw [G10_13_formula]
  exact vasyuninBEntry_10_13_eval

def interval_10_13 : NamedVasyuninInterval :=
{
  h := 10
  k := 13
  lower := (22993523/239770000)
  upper := (23041477/239770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_13_interval
}

theorem G10_14_formula : baezDuarteGramEntry 10 14 = vasyuninBEntry 10 14 := vasyuninBEntry_correct_axiom 10 14

theorem vasyuninBEntry_10_14_eval :
    ((((18160087/199130000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 14) ∧
    (vasyuninBEntry 10 14 ≤ (((18199913/199130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 7 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_14_interval :
    ((((18160087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 14) ∧
    (baezDuarteGramEntry 10 14 ≤ (((18199913/199130000) : ℚ) : ℝ)) := by
  rw [G10_14_formula]
  exact vasyuninBEntry_10_14_eval

def interval_10_14 : NamedVasyuninInterval :=
{
  h := 10
  k := 14
  lower := (18160087/199130000)
  upper := (18199913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_14_interval
}

theorem G10_15_formula : baezDuarteGramEntry 10 15 = vasyuninBEntry 10 15 := vasyuninBEntry_correct_axiom 10 15

theorem vasyuninBEntry_10_15_eval :
    ((((2109169/23935000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 15) ∧
    (vasyuninBEntry 10 15 ≤ (((528489/5983750) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G10_15_interval :
    ((((2109169/23935000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 15) ∧
    (baezDuarteGramEntry 10 15 ≤ (((528489/5983750) : ℚ) : ℝ)) := by
  rw [G10_15_formula]
  exact vasyuninBEntry_10_15_eval

def interval_10_15 : NamedVasyuninInterval :=
{
  h := 10
  k := 15
  lower := (2109169/23935000)
  upper := (528489/5983750)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_15_interval
}

theorem G10_16_formula : baezDuarteGramEntry 10 16 = vasyuninBEntry 10 16 := vasyuninBEntry_correct_axiom 10 16

theorem vasyuninBEntry_10_16_eval :
    ((((1256251/14990000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 16) ∧
    (vasyuninBEntry 10 16 ≤ (((1259249/14990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 8 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_16_interval :
    ((((1256251/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 16) ∧
    (baezDuarteGramEntry 10 16 ≤ (((1259249/14990000) : ℚ) : ℝ)) := by
  rw [G10_16_formula]
  exact vasyuninBEntry_10_16_eval

def interval_10_16 : NamedVasyuninInterval :=
{
  h := 10
  k := 16
  lower := (1256251/14990000)
  upper := (1259249/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_16_interval
}

theorem G10_17_formula : baezDuarteGramEntry 10 17 = vasyuninBEntry 10 17 := vasyuninBEntry_correct_axiom 10 17

theorem vasyuninBEntry_10_17_eval :
    ((((35975501/444990000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 17) ∧
    (vasyuninBEntry 10 17 ≤ (((36064499/444990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1017_formula_bound
  constructor <;> linarith

theorem G10_17_interval :
    ((((35975501/444990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 17) ∧
    (baezDuarteGramEntry 10 17 ≤ (((36064499/444990000) : ℚ) : ℝ)) := by
  rw [G10_17_formula]
  exact vasyuninBEntry_10_17_eval

def interval_10_17 : NamedVasyuninInterval :=
{
  h := 10
  k := 17
  lower := (35975501/444990000)
  upper := (36064499/444990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_17_interval
}

theorem G10_18_formula : baezDuarteGramEntry 10 18 = vasyuninBEntry 10 18 := vasyuninBEntry_correct_axiom 10 18

theorem vasyuninBEntry_10_18_eval :
    ((((8609039/109610000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 18) ∧
    (vasyuninBEntry 10 18 ≤ (((8630961/109610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 9 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_18_interval :
    ((((8609039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 18) ∧
    (baezDuarteGramEntry 10 18 ≤ (((8630961/109610000) : ℚ) : ℝ)) := by
  rw [G10_18_formula]
  exact vasyuninBEntry_10_18_eval

def interval_10_18 : NamedVasyuninInterval :=
{
  h := 10
  k := 18
  lower := (8609039/109610000)
  upper := (8630961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_18_interval
}

theorem G10_19_formula : baezDuarteGramEntry 10 19 = vasyuninBEntry 10 19 := vasyuninBEntry_correct_axiom 10 19

theorem vasyuninBEntry_10_19_eval :
    ((((12617601/163990000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 19) ∧
    (vasyuninBEntry 10 19 ≤ (((12650399/163990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1019_formula_bound
  constructor <;> linarith

theorem G10_19_interval :
    ((((12617601/163990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 19) ∧
    (baezDuarteGramEntry 10 19 ≤ (((12650399/163990000) : ℚ) : ℝ)) := by
  rw [G10_19_formula]
  exact vasyuninBEntry_10_19_eval

def interval_10_19 : NamedVasyuninInterval :=
{
  h := 10
  k := 19
  lower := (12617601/163990000)
  upper := (12650399/163990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_19_interval
}

theorem G10_20_formula : baezDuarteGramEntry 10 20 = vasyuninBEntry 10 20 := vasyuninBEntry_correct_axiom 10 20

theorem vasyuninBEntry_10_20_eval :
    ((((73694443/955570000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 20) ∧
    (vasyuninBEntry 10 20 ≤ (((73885557/955570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 10 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G10_20_interval :
    ((((73694443/955570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 20) ∧
    (baezDuarteGramEntry 10 20 ≤ (((73885557/955570000) : ℚ) : ℝ)) := by
  rw [G10_20_formula]
  exact vasyuninBEntry_10_20_eval

def interval_10_20 : NamedVasyuninInterval :=
{
  h := 10
  k := 20
  lower := (73694443/955570000)
  upper := (73885557/955570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_20_interval
}

theorem G10_21_formula : baezDuarteGramEntry 10 21 = vasyuninBEntry 10 21 := vasyuninBEntry_correct_axiom 10 21

theorem vasyuninBEntry_10_21_eval :
    ((((6974347/96530000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 21) ∧
    (vasyuninBEntry 10 21 ≤ (((6993653/96530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1021_formula_bound
  constructor <;> linarith

theorem G10_21_interval :
    ((((6974347/96530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 21) ∧
    (baezDuarteGramEntry 10 21 ≤ (((6993653/96530000) : ℚ) : ℝ)) := by
  rw [G10_21_formula]
  exact vasyuninBEntry_10_21_eval

def interval_10_21 : NamedVasyuninInterval :=
{
  h := 10
  k := 21
  lower := (6974347/96530000)
  upper := (6993653/96530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_21_interval
}

theorem G10_22_formula : baezDuarteGramEntry 10 22 = vasyuninBEntry 10 22 := vasyuninBEntry_correct_axiom 10 22

theorem vasyuninBEntry_10_22_eval :
    ((((1336269/19310000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 22) ∧
    (vasyuninBEntry 10 22 ≤ (((1340131/19310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 11 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_22_interval :
    ((((1336269/19310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 22) ∧
    (baezDuarteGramEntry 10 22 ≤ (((1340131/19310000) : ℚ) : ℝ)) := by
  rw [G10_22_formula]
  exact vasyuninBEntry_10_22_eval

def interval_10_22 : NamedVasyuninInterval :=
{
  h := 10
  k := 22
  lower := (1336269/19310000)
  upper := (1340131/19310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_22_interval
}

theorem G10_23_formula : baezDuarteGramEntry 10 23 = vasyuninBEntry 10 23 := vasyuninBEntry_correct_axiom 10 23

theorem vasyuninBEntry_10_23_eval :
    ((((60339593/904070000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 23) ∧
    (vasyuninBEntry 10 23 ≤ (((60520407/904070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1023_formula_bound
  constructor <;> linarith

theorem G10_23_interval :
    ((((60339593/904070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 23) ∧
    (baezDuarteGramEntry 10 23 ≤ (((60520407/904070000) : ℚ) : ℝ)) := by
  rw [G10_23_formula]
  exact vasyuninBEntry_10_23_eval

def interval_10_23 : NamedVasyuninInterval :=
{
  h := 10
  k := 23
  lower := (60339593/904070000)
  upper := (60520407/904070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_23_interval
}

theorem G10_24_formula : baezDuarteGramEntry 10 24 = vasyuninBEntry 10 24 := vasyuninBEntry_correct_axiom 10 24

theorem vasyuninBEntry_10_24_eval :
    ((((59527979/920210000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 24) ∧
    (vasyuninBEntry 10 24 ≤ (((59712021/920210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 12 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_24_interval :
    ((((59527979/920210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 24) ∧
    (baezDuarteGramEntry 10 24 ≤ (((59712021/920210000) : ℚ) : ℝ)) := by
  rw [G10_24_formula]
  exact vasyuninBEntry_10_24_eval

def interval_10_24 : NamedVasyuninInterval :=
{
  h := 10
  k := 24
  lower := (59527979/920210000)
  upper := (59712021/920210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_24_interval
}

theorem G10_25_formula : baezDuarteGramEntry 10 25 = vasyuninBEntry 10 25 := vasyuninBEntry_correct_axiom 10 25

theorem vasyuninBEntry_10_25_eval :
    ((((7290461/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 25) ∧
    (vasyuninBEntry 10 25 ≤ (((7313539/115390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G10_25_interval :
    ((((7290461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 25) ∧
    (baezDuarteGramEntry 10 25 ≤ (((7313539/115390000) : ℚ) : ℝ)) := by
  rw [G10_25_formula]
  exact vasyuninBEntry_10_25_eval

def interval_10_25 : NamedVasyuninInterval :=
{
  h := 10
  k := 25
  lower := (7290461/115390000)
  upper := (7313539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_25_interval
}

theorem G10_26_formula : baezDuarteGramEntry 10 26 = vasyuninBEntry 10 26 := vasyuninBEntry_correct_axiom 10 26

theorem vasyuninBEntry_10_26_eval :
    ((((57426181/938190000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 26) ∧
    (vasyuninBEntry 10 26 ≤ (((57613819/938190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 13 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_26_interval :
    ((((57426181/938190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 26) ∧
    (baezDuarteGramEntry 10 26 ≤ (((57613819/938190000) : ℚ) : ℝ)) := by
  rw [G10_26_formula]
  exact vasyuninBEntry_10_26_eval

def interval_10_26 : NamedVasyuninInterval :=
{
  h := 10
  k := 26
  lower := (57426181/938190000)
  upper := (57613819/938190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_26_interval
}

theorem G10_27_formula : baezDuarteGramEntry 10 27 = vasyuninBEntry 10 27 := vasyuninBEntry_correct_axiom 10 27

theorem vasyuninBEntry_10_27_eval :
    ((((13717033/229670000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 27) ∧
    (vasyuninBEntry 10 27 ≤ (((13762967/229670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1027_formula_bound
  constructor <;> linarith

theorem G10_27_interval :
    ((((13717033/229670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 27) ∧
    (baezDuarteGramEntry 10 27 ≤ (((13762967/229670000) : ℚ) : ℝ)) := by
  rw [G10_27_formula]
  exact vasyuninBEntry_10_27_eval

def interval_10_27 : NamedVasyuninInterval :=
{
  h := 10
  k := 27
  lower := (13717033/229670000)
  upper := (13762967/229670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_27_interval
}

theorem G10_28_formula : baezDuarteGramEntry 10 28 = vasyuninBEntry 10 28 := vasyuninBEntry_correct_axiom 10 28

theorem vasyuninBEntry_10_28_eval :
    ((((1922713/32870000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 28) ∧
    (vasyuninBEntry 10 28 ≤ (((1929287/32870000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 14 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_28_interval :
    ((((1922713/32870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 28) ∧
    (baezDuarteGramEntry 10 28 ≤ (((1929287/32870000) : ℚ) : ℝ)) := by
  rw [G10_28_formula]
  exact vasyuninBEntry_10_28_eval

def interval_10_28 : NamedVasyuninInterval :=
{
  h := 10
  k := 28
  lower := (1922713/32870000)
  upper := (1929287/32870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_28_interval
}

theorem G10_29_formula : baezDuarteGramEntry 10 29 = vasyuninBEntry 10 29 := vasyuninBEntry_correct_axiom 10 29

theorem vasyuninBEntry_10_29_eval :
    ((((10078489/175110000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 29) ∧
    (vasyuninBEntry 10 29 ≤ (((10113511/175110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1029_formula_bound
  constructor <;> linarith

theorem G10_29_interval :
    ((((10078489/175110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 29) ∧
    (baezDuarteGramEntry 10 29 ≤ (((10113511/175110000) : ℚ) : ℝ)) := by
  rw [G10_29_formula]
  exact vasyuninBEntry_10_29_eval

def interval_10_29 : NamedVasyuninInterval :=
{
  h := 10
  k := 29
  lower := (10078489/175110000)
  upper := (10113511/175110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_29_interval
}

theorem G10_30_formula : baezDuarteGramEntry 10 30 = vasyuninBEntry 10 30 := vasyuninBEntry_correct_axiom 10 30

theorem vasyuninBEntry_10_30_eval :
    ((((53766331/936690000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 30) ∧
    (vasyuninBEntry 10 30 ≤ (((53953669/936690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 10 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G10_30_interval :
    ((((53766331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 30) ∧
    (baezDuarteGramEntry 10 30 ≤ (((53953669/936690000) : ℚ) : ℝ)) := by
  rw [G10_30_formula]
  exact vasyuninBEntry_10_30_eval

def interval_10_30 : NamedVasyuninInterval :=
{
  h := 10
  k := 30
  lower := (53766331/936690000)
  upper := (53953669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_30_interval
}

theorem G10_31_formula : baezDuarteGramEntry 10 31 = vasyuninBEntry 10 31 := vasyuninBEntry_correct_axiom 10 31

theorem vasyuninBEntry_10_31_eval :
    ((((2198003/39970000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 31) ∧
    (vasyuninBEntry 10 31 ≤ (((2205997/39970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1031_formula_bound
  constructor <;> linarith

theorem G10_31_interval :
    ((((2198003/39970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 31) ∧
    (baezDuarteGramEntry 10 31 ≤ (((2205997/39970000) : ℚ) : ℝ)) := by
  rw [G10_31_formula]
  exact vasyuninBEntry_10_31_eval

def interval_10_31 : NamedVasyuninInterval :=
{
  h := 10
  k := 31
  lower := (2198003/39970000)
  upper := (2205997/39970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_31_interval
}

theorem G10_32_formula : baezDuarteGramEntry 10 32 = vasyuninBEntry 10 32 := vasyuninBEntry_correct_axiom 10 32

theorem vasyuninBEntry_10_32_eval :
    ((((15825353/296470000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 32) ∧
    (vasyuninBEntry 10 32 ≤ (((15884647/296470000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 16 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_32_interval :
    ((((15825353/296470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 32) ∧
    (baezDuarteGramEntry 10 32 ≤ (((15884647/296470000) : ℚ) : ℝ)) := by
  rw [G10_32_formula]
  exact vasyuninBEntry_10_32_eval

def interval_10_32 : NamedVasyuninInterval :=
{
  h := 10
  k := 32
  lower := (15825353/296470000)
  upper := (15884647/296470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_32_interval
}

theorem G10_33_formula : baezDuarteGramEntry 10 33 = vasyuninBEntry 10 33 := vasyuninBEntry_correct_axiom 10 33

theorem vasyuninBEntry_10_33_eval :
    ((((25471043/489570000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 33) ∧
    (vasyuninBEntry 10 33 ≤ (((25568957/489570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1033_formula_bound
  constructor <;> linarith

theorem G10_33_interval :
    ((((25471043/489570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 33) ∧
    (baezDuarteGramEntry 10 33 ≤ (((25568957/489570000) : ℚ) : ℝ)) := by
  rw [G10_33_formula]
  exact vasyuninBEntry_10_33_eval

def interval_10_33 : NamedVasyuninInterval :=
{
  h := 10
  k := 33
  lower := (25471043/489570000)
  upper := (25568957/489570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_33_interval
}

theorem G10_34_formula : baezDuarteGramEntry 10 34 = vasyuninBEntry 10 34 := vasyuninBEntry_correct_axiom 10 34

theorem vasyuninBEntry_10_34_eval :
    ((((21812113/428870000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 34) ∧
    (vasyuninBEntry 10 34 ≤ (((21897887/428870000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 17 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_34_interval :
    ((((21812113/428870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 34) ∧
    (baezDuarteGramEntry 10 34 ≤ (((21897887/428870000) : ℚ) : ℝ)) := by
  rw [G10_34_formula]
  exact vasyuninBEntry_10_34_eval

def interval_10_34 : NamedVasyuninInterval :=
{
  h := 10
  k := 34
  lower := (21812113/428870000)
  upper := (21897887/428870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_34_interval
}

theorem G10_35_formula : baezDuarteGramEntry 10 35 = vasyuninBEntry 10 35 := vasyuninBEntry_correct_axiom 10 35

theorem vasyuninBEntry_10_35_eval :
    ((((195329/3910000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 35) ∧
    (vasyuninBEntry 10 35 ≤ (((196111/3910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 7 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G10_35_interval :
    ((((195329/3910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 35) ∧
    (baezDuarteGramEntry 10 35 ≤ (((196111/3910000) : ℚ) : ℝ)) := by
  rw [G10_35_formula]
  exact vasyuninBEntry_10_35_eval

def interval_10_35 : NamedVasyuninInterval :=
{
  h := 10
  k := 35
  lower := (195329/3910000)
  upper := (196111/3910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_35_interval
}

theorem G10_36_formula : baezDuarteGramEntry 10 36 = vasyuninBEntry 10 36 := vasyuninBEntry_correct_axiom 10 36

theorem vasyuninBEntry_10_36_eval :
    ((((7985639/163610000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 36) ∧
    (vasyuninBEntry 10 36 ≤ (((8018361/163610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_18_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 18 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_36_interval :
    ((((7985639/163610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 36) ∧
    (baezDuarteGramEntry 10 36 ≤ (((8018361/163610000) : ℚ) : ℝ)) := by
  rw [G10_36_formula]
  exact vasyuninBEntry_10_36_eval

def interval_10_36 : NamedVasyuninInterval :=
{
  h := 10
  k := 36
  lower := (7985639/163610000)
  upper := (8018361/163610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_36_interval
}

theorem G10_37_formula : baezDuarteGramEntry 10 37 = vasyuninBEntry 10 37 := vasyuninBEntry_correct_axiom 10 37

theorem vasyuninBEntry_10_37_eval :
    ((((6596231/137690000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 37) ∧
    (vasyuninBEntry 10 37 ≤ (((6623769/137690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1037_formula_bound
  constructor <;> linarith

theorem G10_37_interval :
    ((((6596231/137690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 37) ∧
    (baezDuarteGramEntry 10 37 ≤ (((6623769/137690000) : ℚ) : ℝ)) := by
  rw [G10_37_formula]
  exact vasyuninBEntry_10_37_eval

def interval_10_37 : NamedVasyuninInterval :=
{
  h := 10
  k := 37
  lower := (6596231/137690000)
  upper := (6623769/137690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_37_interval
}

theorem G10_38_formula : baezDuarteGramEntry 10 38 = vasyuninBEntry 10 38 := vasyuninBEntry_correct_axiom 10 38

theorem vasyuninBEntry_10_38_eval :
    ((((18859987/400130000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 38) ∧
    (vasyuninBEntry 10 38 ≤ (((18940013/400130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_38_interval :
    ((((18859987/400130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 38) ∧
    (baezDuarteGramEntry 10 38 ≤ (((18940013/400130000) : ℚ) : ℝ)) := by
  rw [G10_38_formula]
  exact vasyuninBEntry_10_38_eval

def interval_10_38 : NamedVasyuninInterval :=
{
  h := 10
  k := 38
  lower := (18859987/400130000)
  upper := (18940013/400130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_38_interval
}

theorem G10_39_formula : baezDuarteGramEntry 10 39 = vasyuninBEntry 10 39 := vasyuninBEntry_correct_axiom 10 39

theorem vasyuninBEntry_10_39_eval :
    ((((9280051/199490000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 39) ∧
    (vasyuninBEntry 10 39 ≤ (((9319949/199490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1039_formula_bound
  constructor <;> linarith

theorem G10_39_interval :
    ((((9280051/199490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 39) ∧
    (baezDuarteGramEntry 10 39 ≤ (((9319949/199490000) : ℚ) : ℝ)) := by
  rw [G10_39_formula]
  exact vasyuninBEntry_10_39_eval

def interval_10_39 : NamedVasyuninInterval :=
{
  h := 10
  k := 39
  lower := (9280051/199490000)
  upper := (9319949/199490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_39_interval
}

theorem G10_40_formula : baezDuarteGramEntry 10 40 = vasyuninBEntry 10 40 := vasyuninBEntry_correct_axiom 10 40

theorem vasyuninBEntry_10_40_eval :
    ((((10908959/235410000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 40) ∧
    (vasyuninBEntry 10 40 ≤ (((10956041/235410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 10 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G10_40_interval :
    ((((10908959/235410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 40) ∧
    (baezDuarteGramEntry 10 40 ≤ (((10956041/235410000) : ℚ) : ℝ)) := by
  rw [G10_40_formula]
  exact vasyuninBEntry_10_40_eval

def interval_10_40 : NamedVasyuninInterval :=
{
  h := 10
  k := 40
  lower := (10908959/235410000)
  upper := (10956041/235410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_40_interval
}

theorem G10_41_formula : baezDuarteGramEntry 10 41 = vasyuninBEntry 10 41 := vasyuninBEntry_correct_axiom 10 41

theorem vasyuninBEntry_10_41_eval :
    ((((40180489/895110000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 41) ∧
    (vasyuninBEntry 10 41 ≤ (((40359511/895110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1041_formula_bound
  constructor <;> linarith

theorem G10_41_interval :
    ((((40180489/895110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 41) ∧
    (baezDuarteGramEntry 10 41 ≤ (((40359511/895110000) : ℚ) : ℝ)) := by
  rw [G10_41_formula]
  exact vasyuninBEntry_10_41_eval

def interval_10_41 : NamedVasyuninInterval :=
{
  h := 10
  k := 41
  lower := (40180489/895110000)
  upper := (40359511/895110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_41_interval
}

theorem G10_42_formula : baezDuarteGramEntry 10 42 = vasyuninBEntry 10 42 := vasyuninBEntry_correct_axiom 10 42

theorem vasyuninBEntry_10_42_eval :
    ((((190441/4340000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 42) ∧
    (vasyuninBEntry 10 42 ≤ (((191309/4340000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 21 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_42_interval :
    ((((190441/4340000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 42) ∧
    (baezDuarteGramEntry 10 42 ≤ (((191309/4340000) : ℚ) : ℝ)) := by
  rw [G10_42_formula]
  exact vasyuninBEntry_10_42_eval

def interval_10_42 : NamedVasyuninInterval :=
{
  h := 10
  k := 42
  lower := (190441/4340000)
  upper := (191309/4340000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_42_interval
}

theorem G10_43_formula : baezDuarteGramEntry 10 43 = vasyuninBEntry 10 43 := vasyuninBEntry_correct_axiom 10 43

theorem vasyuninBEntry_10_43_eval :
    ((((36375437/845630000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 43) ∧
    (vasyuninBEntry 10 43 ≤ (((36544563/845630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1043_formula_bound
  constructor <;> linarith

theorem G10_43_interval :
    ((((36375437/845630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 43) ∧
    (baezDuarteGramEntry 10 43 ≤ (((36544563/845630000) : ℚ) : ℝ)) := by
  rw [G10_43_formula]
  exact vasyuninBEntry_10_43_eval

def interval_10_43 : NamedVasyuninInterval :=
{
  h := 10
  k := 43
  lower := (36375437/845630000)
  upper := (36544563/845630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_43_interval
}

theorem G10_44_formula : baezDuarteGramEntry 10 44 = vasyuninBEntry 10 44 := vasyuninBEntry_correct_axiom 10 44

theorem vasyuninBEntry_10_44_eval :
    ((((6888697/163030000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 44) ∧
    (vasyuninBEntry 10 44 ≤ (((6921303/163030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 22 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_44_interval :
    ((((6888697/163030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 44) ∧
    (baezDuarteGramEntry 10 44 ≤ (((6921303/163030000) : ℚ) : ℝ)) := by
  rw [G10_44_formula]
  exact vasyuninBEntry_10_44_eval

def interval_10_44 : NamedVasyuninInterval :=
{
  h := 10
  k := 44
  lower := (6888697/163030000)
  upper := (6921303/163030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_44_interval
}

theorem G10_45_formula : baezDuarteGramEntry 10 45 = vasyuninBEntry 10 45 := vasyuninBEntry_correct_axiom 10 45

theorem vasyuninBEntry_10_45_eval :
    ((((1503889/36110000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 45) ∧
    (vasyuninBEntry 10 45 ≤ (((1511111/36110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 9 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G10_45_interval :
    ((((1503889/36110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 45) ∧
    (baezDuarteGramEntry 10 45 ≤ (((1511111/36110000) : ℚ) : ℝ)) := by
  rw [G10_45_formula]
  exact vasyuninBEntry_10_45_eval

def interval_10_45 : NamedVasyuninInterval :=
{
  h := 10
  k := 45
  lower := (1503889/36110000)
  upper := (1511111/36110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_45_interval
}

theorem G10_46_formula : baezDuarteGramEntry 10 46 = vasyuninBEntry 10 46 := vasyuninBEntry_correct_axiom 10 46

theorem vasyuninBEntry_10_46_eval :
    ((((39124317/956830000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 46) ∧
    (vasyuninBEntry 10 46 ≤ (((39315683/956830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_46_interval :
    ((((39124317/956830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 46) ∧
    (baezDuarteGramEntry 10 46 ≤ (((39315683/956830000) : ℚ) : ℝ)) := by
  rw [G10_46_formula]
  exact vasyuninBEntry_10_46_eval

def interval_10_46 : NamedVasyuninInterval :=
{
  h := 10
  k := 46
  lower := (39124317/956830000)
  upper := (39315683/956830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_46_interval
}

theorem G10_47_formula : baezDuarteGramEntry 10 47 = vasyuninBEntry 10 47 := vasyuninBEntry_correct_axiom 10 47

theorem vasyuninBEntry_10_47_eval :
    ((((39142817/971830000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 47) ∧
    (vasyuninBEntry 10 47 ≤ (((39337183/971830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1047_formula_bound
  constructor <;> linarith

theorem G10_47_interval :
    ((((39142817/971830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 47) ∧
    (baezDuarteGramEntry 10 47 ≤ (((39337183/971830000) : ℚ) : ℝ)) := by
  rw [G10_47_formula]
  exact vasyuninBEntry_10_47_eval

def interval_10_47 : NamedVasyuninInterval :=
{
  h := 10
  k := 47
  lower := (39142817/971830000)
  upper := (39337183/971830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_47_interval
}

theorem G10_48_formula : baezDuarteGramEntry 10 48 = vasyuninBEntry 10 48 := vasyuninBEntry_correct_axiom 10 48

theorem vasyuninBEntry_10_48_eval :
    ((((790511/19890000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 48) ∧
    (vasyuninBEntry 10 48 ≤ (((794489/19890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 24 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G10_48_interval :
    ((((790511/19890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 48) ∧
    (baezDuarteGramEntry 10 48 ≤ (((794489/19890000) : ℚ) : ℝ)) := by
  rw [G10_48_formula]
  exact vasyuninBEntry_10_48_eval

def interval_10_48 : NamedVasyuninInterval :=
{
  h := 10
  k := 48
  lower := (790511/19890000)
  upper := (794489/19890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_48_interval
}

theorem G10_49_formula : baezDuarteGramEntry 10 49 = vasyuninBEntry 10 49 := vasyuninBEntry_correct_axiom 10 49

theorem vasyuninBEntry_10_49_eval :
    ((((2877679/73210000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 49) ∧
    (vasyuninBEntry 10 49 ≤ (((2892321/73210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1049_formula_bound
  constructor <;> linarith

theorem G10_49_interval :
    ((((2877679/73210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 49) ∧
    (baezDuarteGramEntry 10 49 ≤ (((2892321/73210000) : ℚ) : ℝ)) := by
  rw [G10_49_formula]
  exact vasyuninBEntry_10_49_eval

def interval_10_49 : NamedVasyuninInterval :=
{
  h := 10
  k := 49
  lower := (2877679/73210000)
  upper := (2892321/73210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_49_interval
}

theorem G10_50_formula : baezDuarteGramEntry 10 50 = vasyuninBEntry 10 50 := vasyuninBEntry_correct_axiom 10 50

theorem vasyuninBEntry_10_50_eval :
    ((((35519269/907310000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 50) ∧
    (vasyuninBEntry 10 50 ≤ (((35700731/907310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 10 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G10_50_interval :
    ((((35519269/907310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 50) ∧
    (baezDuarteGramEntry 10 50 ≤ (((35700731/907310000) : ℚ) : ℝ)) := by
  rw [G10_50_formula]
  exact vasyuninBEntry_10_50_eval

def interval_10_50 : NamedVasyuninInterval :=
{
  h := 10
  k := 50
  lower := (35519269/907310000)
  upper := (35700731/907310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_50_interval
}

theorem G11_1_formula : baezDuarteGramEntry 11 1 = vasyuninBEntry 1 11 := by
  rw [baezDuarteGramEntry_symm 11 1]
  exact G1_11_formula

theorem G11_1_interval :
    ((((12924551/60740000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 1) ∧
    (baezDuarteGramEntry 11 1 ≤ (((12936699/60740000) : ℚ) : ℝ)) := by
  rw [G11_1_formula]
  exact vasyuninBEntry_1_11_eval

def interval_11_1 : NamedVasyuninInterval :=
{
  h := 11
  k := 1
  lower := (12924551/60740000)
  upper := (12936699/60740000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_1_interval
}

theorem G11_2_formula : baezDuarteGramEntry 11 2 = vasyuninBEntry 2 11 := by
  rw [baezDuarteGramEntry_symm 11 2]
  exact G2_11_formula

theorem G11_2_interval :
    ((((146398607/813930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 2) ∧
    (baezDuarteGramEntry 11 2 ≤ (((146561393/813930000) : ℚ) : ℝ)) := by
  rw [G11_2_formula]
  exact vasyuninBEntry_2_11_eval

def interval_11_2 : NamedVasyuninInterval :=
{
  h := 11
  k := 2
  lower := (146398607/813930000)
  upper := (146561393/813930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_2_interval
}

theorem G11_3_formula : baezDuarteGramEntry 11 3 = vasyuninBEntry 3 11 := by
  rw [baezDuarteGramEntry_symm 11 3]
  exact G3_11_formula

theorem G11_3_interval :
    ((((142731359/886410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 3) ∧
    (baezDuarteGramEntry 11 3 ≤ (((142908641/886410000) : ℚ) : ℝ)) := by
  rw [G11_3_formula]
  exact vasyuninBEntry_3_11_eval

def interval_11_3 : NamedVasyuninInterval :=
{
  h := 11
  k := 3
  lower := (142731359/886410000)
  upper := (142908641/886410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_3_interval
}

theorem G11_4_formula : baezDuarteGramEntry 11 4 = vasyuninBEntry 4 11 := by
  rw [baezDuarteGramEntry_symm 11 4]
  exact G4_11_formula

theorem G11_4_interval :
    ((((4931041/33340000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 4) ∧
    (baezDuarteGramEntry 11 4 ≤ (((4937709/33340000) : ℚ) : ℝ)) := by
  rw [G11_4_formula]
  exact vasyuninBEntry_4_11_eval

def interval_11_4 : NamedVasyuninInterval :=
{
  h := 11
  k := 4
  lower := (4931041/33340000)
  upper := (4937709/33340000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_4_interval
}

theorem G11_5_formula : baezDuarteGramEntry 11 5 = vasyuninBEntry 5 11 := by
  rw [baezDuarteGramEntry_symm 11 5]
  exact G5_11_formula

theorem G11_5_interval :
    ((((47031043/339570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 5) ∧
    (baezDuarteGramEntry 11 5 ≤ (((47098957/339570000) : ℚ) : ℝ)) := by
  rw [G11_5_formula]
  exact vasyuninBEntry_5_11_eval

def interval_11_5 : NamedVasyuninInterval :=
{
  h := 11
  k := 5
  lower := (47031043/339570000)
  upper := (47098957/339570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_5_interval
}

theorem G11_6_formula : baezDuarteGramEntry 11 6 = vasyuninBEntry 6 11 := by
  rw [baezDuarteGramEntry_symm 11 6]
  exact G6_11_formula

theorem G11_6_interval :
    ((((38255551/294490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 6) ∧
    (baezDuarteGramEntry 11 6 ≤ (((38314449/294490000) : ℚ) : ℝ)) := by
  rw [G11_6_formula]
  exact vasyuninBEntry_6_11_eval

def interval_11_6 : NamedVasyuninInterval :=
{
  h := 11
  k := 6
  lower := (38255551/294490000)
  upper := (38314449/294490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_6_interval
}

theorem G11_7_formula : baezDuarteGramEntry 11 7 = vasyuninBEntry 7 11 := by
  rw [baezDuarteGramEntry_symm 11 7]
  exact G7_11_formula

theorem G11_7_interval :
    ((((96270517/794830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 7) ∧
    (baezDuarteGramEntry 11 7 ≤ (((96429483/794830000) : ℚ) : ℝ)) := by
  rw [G11_7_formula]
  exact vasyuninBEntry_7_11_eval

def interval_11_7 : NamedVasyuninInterval :=
{
  h := 11
  k := 7
  lower := (96270517/794830000)
  upper := (96429483/794830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_7_interval
}

theorem G11_8_formula : baezDuarteGramEntry 11 8 = vasyuninBEntry 8 11 := by
  rw [baezDuarteGramEntry_symm 11 8]
  exact G8_11_formula

theorem G11_8_interval :
    ((((27808387/241130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 8) ∧
    (baezDuarteGramEntry 11 8 ≤ (((27856613/241130000) : ℚ) : ℝ)) := by
  rw [G11_8_formula]
  exact vasyuninBEntry_8_11_eval

def interval_11_8 : NamedVasyuninInterval :=
{
  h := 11
  k := 8
  lower := (27808387/241130000)
  upper := (27856613/241130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_8_interval
}

theorem G11_9_formula : baezDuarteGramEntry 11 9 = vasyuninBEntry 9 11 := by
  rw [baezDuarteGramEntry_symm 11 9]
  exact G9_11_formula

theorem G11_9_interval :
    ((((5335219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 9) ∧
    (baezDuarteGramEntry 11 9 ≤ (((5344781/47810000) : ℚ) : ℝ)) := by
  rw [G11_9_formula]
  exact vasyuninBEntry_9_11_eval

def interval_11_9 : NamedVasyuninInterval :=
{
  h := 11
  k := 9
  lower := (5335219/47810000)
  upper := (5344781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_9_interval
}

theorem G11_10_formula : baezDuarteGramEntry 11 10 = vasyuninBEntry 10 11 := by
  rw [baezDuarteGramEntry_symm 11 10]
  exact G10_11_formula

theorem G11_10_interval :
    ((((79467961/720390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 10) ∧
    (baezDuarteGramEntry 11 10 ≤ (((79612039/720390000) : ℚ) : ℝ)) := by
  rw [G11_10_formula]
  exact vasyuninBEntry_10_11_eval

def interval_11_10 : NamedVasyuninInterval :=
{
  h := 11
  k := 10
  lower := (79467961/720390000)
  upper := (79612039/720390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_10_interval
}

theorem G11_11_formula_eq : baezDuarteGramEntry 11 11 = (1 / (11 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 11 := by norm_num
  rw [baez_duarte_diagonal_scaling 11 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G11_11_log_gamma_interval :
  ((((79880239/697610000) : ℚ) : ℝ) ≤ (1 / (11 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (11 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((80019761/697610000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 11 (by norm_num)
  constructor
  · have : ((((79880239/697610000) : ℚ) : ℝ) ≤ (1 / (11 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (11 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((80019761/697610000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G11_11_interval : ((((79880239/697610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 11) ∧ (baezDuarteGramEntry 11 11 ≤ (((80019761/697610000) : ℚ) : ℝ)) := by
  rw [G11_11_formula_eq]
  exact G11_11_log_gamma_interval

def interval_11_11 : NamedVasyuninInterval :=
{
  h := 11
  k := 11
  lower := (79880239/697610000)
  upper := (80019761/697610000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G11_11_interval
}

theorem G11_12_formula : baezDuarteGramEntry 11 12 = vasyuninBEntry 11 12 := vasyuninBEntry_correct_axiom 11 12

theorem vasyuninBEntry_11_12_eval :
    ((((36858559/364410000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 12) ∧
    (vasyuninBEntry 11 12 ≤ (((36931441/364410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1112_formula_bound
  constructor <;> linarith

theorem G11_12_interval :
    ((((36858559/364410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 12) ∧
    (baezDuarteGramEntry 11 12 ≤ (((36931441/364410000) : ℚ) : ℝ)) := by
  rw [G11_12_formula]
  exact vasyuninBEntry_11_12_eval

def interval_11_12 : NamedVasyuninInterval :=
{
  h := 11
  k := 12
  lower := (36858559/364410000)
  upper := (36931441/364410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_12_interval
}

theorem G11_13_formula : baezDuarteGramEntry 11 13 = vasyuninBEntry 11 13 := vasyuninBEntry_correct_axiom 11 13

theorem vasyuninBEntry_11_13_eval :
    ((((27340857/291430000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 13) ∧
    (vasyuninBEntry 11 13 ≤ (((27399143/291430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1113_formula_bound
  constructor <;> linarith

theorem G11_13_interval :
    ((((27340857/291430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 13) ∧
    (baezDuarteGramEntry 11 13 ≤ (((27399143/291430000) : ℚ) : ℝ)) := by
  rw [G11_13_formula]
  exact vasyuninBEntry_11_13_eval

def interval_11_13 : NamedVasyuninInterval :=
{
  h := 11
  k := 13
  lower := (27340857/291430000)
  upper := (27399143/291430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_13_interval
}

theorem G11_14_formula : baezDuarteGramEntry 11 14 = vasyuninBEntry 11 14 := vasyuninBEntry_correct_axiom 11 14

theorem vasyuninBEntry_11_14_eval :
    ((((52111121/588790000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 14) ∧
    (vasyuninBEntry 11 14 ≤ (((52228879/588790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1114_formula_bound
  constructor <;> linarith

theorem G11_14_interval :
    ((((52111121/588790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 14) ∧
    (baezDuarteGramEntry 11 14 ≤ (((52228879/588790000) : ℚ) : ℝ)) := by
  rw [G11_14_formula]
  exact vasyuninBEntry_11_14_eval

def interval_11_14 : NamedVasyuninInterval :=
{
  h := 11
  k := 14
  lower := (52111121/588790000)
  upper := (52228879/588790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_14_interval
}

theorem G11_15_formula : baezDuarteGramEntry 11 15 = vasyuninBEntry 11 15 := vasyuninBEntry_correct_axiom 11 15

theorem vasyuninBEntry_11_15_eval :
    ((((130283/1545000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 15) ∧
    (vasyuninBEntry 11 15 ≤ (((16324/193125) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1115_formula_bound
  constructor <;> linarith

theorem G11_15_interval :
    ((((130283/1545000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 15) ∧
    (baezDuarteGramEntry 11 15 ≤ (((16324/193125) : ℚ) : ℝ)) := by
  rw [G11_15_formula]
  exact vasyuninBEntry_11_15_eval

def interval_11_15 : NamedVasyuninInterval :=
{
  h := 11
  k := 15
  lower := (130283/1545000)
  upper := (16324/193125)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_15_interval
}

theorem G11_16_formula : baezDuarteGramEntry 11 16 = vasyuninBEntry 11 16 := vasyuninBEntry_correct_axiom 11 16

theorem vasyuninBEntry_11_16_eval :
    ((((21553381/266190000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 16) ∧
    (vasyuninBEntry 11 16 ≤ (((21606619/266190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1116_formula_bound
  constructor <;> linarith

theorem G11_16_interval :
    ((((21553381/266190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 16) ∧
    (baezDuarteGramEntry 11 16 ≤ (((21606619/266190000) : ℚ) : ℝ)) := by
  rw [G11_16_formula]
  exact vasyuninBEntry_11_16_eval

def interval_11_16 : NamedVasyuninInterval :=
{
  h := 11
  k := 16
  lower := (21553381/266190000)
  upper := (21606619/266190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_16_interval
}

theorem G11_17_formula : baezDuarteGramEntry 11 17 = vasyuninBEntry 11 17 := vasyuninBEntry_correct_axiom 11 17

theorem vasyuninBEntry_11_17_eval :
    ((((3587397/46030000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 17) ∧
    (vasyuninBEntry 11 17 ≤ (((3596603/46030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1117_formula_bound
  constructor <;> linarith

theorem G11_17_interval :
    ((((3587397/46030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 17) ∧
    (baezDuarteGramEntry 11 17 ≤ (((3596603/46030000) : ℚ) : ℝ)) := by
  rw [G11_17_formula]
  exact vasyuninBEntry_11_17_eval

def interval_11_17 : NamedVasyuninInterval :=
{
  h := 11
  k := 17
  lower := (3587397/46030000)
  upper := (3596603/46030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_17_interval
}

theorem G11_18_formula : baezDuarteGramEntry 11 18 = vasyuninBEntry 11 18 := vasyuninBEntry_correct_axiom 11 18

theorem vasyuninBEntry_11_18_eval :
    ((((32107257/427430000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 18) ∧
    (vasyuninBEntry 11 18 ≤ (((32192743/427430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1118_formula_bound
  constructor <;> linarith

theorem G11_18_interval :
    ((((32107257/427430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 18) ∧
    (baezDuarteGramEntry 11 18 ≤ (((32192743/427430000) : ℚ) : ℝ)) := by
  rw [G11_18_formula]
  exact vasyuninBEntry_11_18_eval

def interval_11_18 : NamedVasyuninInterval :=
{
  h := 11
  k := 18
  lower := (32107257/427430000)
  upper := (32192743/427430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_18_interval
}

theorem G11_19_formula : baezDuarteGramEntry 11 19 = vasyuninBEntry 11 19 := vasyuninBEntry_correct_axiom 11 19

theorem vasyuninBEntry_11_19_eval :
    ((((1617779/22210000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 19) ∧
    (vasyuninBEntry 11 19 ≤ (((1622221/22210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1119_formula_bound
  constructor <;> linarith

theorem G11_19_interval :
    ((((1617779/22210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 19) ∧
    (baezDuarteGramEntry 11 19 ≤ (((1622221/22210000) : ℚ) : ℝ)) := by
  rw [G11_19_formula]
  exact vasyuninBEntry_11_19_eval

def interval_11_19 : NamedVasyuninInterval :=
{
  h := 11
  k := 19
  lower := (1617779/22210000)
  upper := (1622221/22210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_19_interval
}

theorem G11_20_formula : baezDuarteGramEntry 11 20 = vasyuninBEntry 11 20 := vasyuninBEntry_correct_axiom 11 20

theorem vasyuninBEntry_11_20_eval :
    ((((38505797/542030000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 20) ∧
    (vasyuninBEntry 11 20 ≤ (((38614203/542030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1120_formula_bound
  constructor <;> linarith

theorem G11_20_interval :
    ((((38505797/542030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 20) ∧
    (baezDuarteGramEntry 11 20 ≤ (((38614203/542030000) : ℚ) : ℝ)) := by
  rw [G11_20_formula]
  exact vasyuninBEntry_11_20_eval

def interval_11_20 : NamedVasyuninInterval :=
{
  h := 11
  k := 20
  lower := (38505797/542030000)
  upper := (38614203/542030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_20_interval
}

theorem G11_21_formula : baezDuarteGramEntry 11 21 = vasyuninBEntry 11 21 := vasyuninBEntry_correct_axiom 11 21

theorem vasyuninBEntry_11_21_eval :
    ((((17212859/246410000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 21) ∧
    (vasyuninBEntry 11 21 ≤ (((17262141/246410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1121_formula_bound
  constructor <;> linarith

theorem G11_21_interval :
    ((((17212859/246410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 21) ∧
    (baezDuarteGramEntry 11 21 ≤ (((17262141/246410000) : ℚ) : ℝ)) := by
  rw [G11_21_formula]
  exact vasyuninBEntry_11_21_eval

def interval_11_21 : NamedVasyuninInterval :=
{
  h := 11
  k := 21
  lower := (17212859/246410000)
  upper := (17262141/246410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_21_interval
}

theorem G11_22_formula : baezDuarteGramEntry 11 22 = vasyuninBEntry 11 22 := vasyuninBEntry_correct_axiom 11 22

theorem vasyuninBEntry_11_22_eval :
    ((((41151297/587030000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 22) ∧
    (vasyuninBEntry 11 22 ≤ (((41268703/587030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 11 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 11)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 11)
  constructor <;> linarith

theorem G11_22_interval :
    ((((41151297/587030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 22) ∧
    (baezDuarteGramEntry 11 22 ≤ (((41268703/587030000) : ℚ) : ℝ)) := by
  rw [G11_22_formula]
  exact vasyuninBEntry_11_22_eval

def interval_11_22 : NamedVasyuninInterval :=
{
  h := 11
  k := 22
  lower := (41151297/587030000)
  upper := (41268703/587030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_22_interval
}

theorem G11_23_formula : baezDuarteGramEntry 11 23 = vasyuninBEntry 11 23 := vasyuninBEntry_correct_axiom 11 23

theorem vasyuninBEntry_11_23_eval :
    ((((1953439/29610000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 23) ∧
    (vasyuninBEntry 11 23 ≤ (((1959361/29610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1123_formula_bound
  constructor <;> linarith

theorem G11_23_interval :
    ((((1953439/29610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 23) ∧
    (baezDuarteGramEntry 11 23 ≤ (((1959361/29610000) : ℚ) : ℝ)) := by
  rw [G11_23_formula]
  exact vasyuninBEntry_11_23_eval

def interval_11_23 : NamedVasyuninInterval :=
{
  h := 11
  k := 23
  lower := (1953439/29610000)
  upper := (1959361/29610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_23_interval
}

theorem G11_24_formula : baezDuarteGramEntry 11 24 = vasyuninBEntry 11 24 := vasyuninBEntry_correct_axiom 11 24

theorem vasyuninBEntry_11_24_eval :
    ((((27746189/438110000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 24) ∧
    (vasyuninBEntry 11 24 ≤ (((27833811/438110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1124_formula_bound
  constructor <;> linarith

theorem G11_24_interval :
    ((((27746189/438110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 24) ∧
    (baezDuarteGramEntry 11 24 ≤ (((27833811/438110000) : ℚ) : ℝ)) := by
  rw [G11_24_formula]
  exact vasyuninBEntry_11_24_eval

def interval_11_24 : NamedVasyuninInterval :=
{
  h := 11
  k := 24
  lower := (27746189/438110000)
  upper := (27833811/438110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_24_interval
}

theorem G11_25_formula : baezDuarteGramEntry 11 25 = vasyuninBEntry 11 25 := vasyuninBEntry_correct_axiom 11 25

theorem vasyuninBEntry_11_25_eval :
    ((((360611/5890000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 25) ∧
    (vasyuninBEntry 11 25 ≤ (((361789/5890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1125_formula_bound
  constructor <;> linarith

theorem G11_25_interval :
    ((((360611/5890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 25) ∧
    (baezDuarteGramEntry 11 25 ≤ (((361789/5890000) : ℚ) : ℝ)) := by
  rw [G11_25_formula]
  exact vasyuninBEntry_11_25_eval

def interval_11_25 : NamedVasyuninInterval :=
{
  h := 11
  k := 25
  lower := (360611/5890000)
  upper := (361789/5890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_25_interval
}

theorem G11_26_formula : baezDuarteGramEntry 11 26 = vasyuninBEntry 11 26 := vasyuninBEntry_correct_axiom 11 26

theorem vasyuninBEntry_11_26_eval :
    ((((1793857/30180000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 26) ∧
    (vasyuninBEntry 11 26 ≤ (((1799893/30180000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1126_formula_bound
  constructor <;> linarith

theorem G11_26_interval :
    ((((1793857/30180000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 26) ∧
    (baezDuarteGramEntry 11 26 ≤ (((1799893/30180000) : ℚ) : ℝ)) := by
  rw [G11_26_formula]
  exact vasyuninBEntry_11_26_eval

def interval_11_26 : NamedVasyuninInterval :=
{
  h := 11
  k := 26
  lower := (1793857/30180000)
  upper := (1799893/30180000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_26_interval
}

theorem G11_27_formula : baezDuarteGramEntry 11 27 = vasyuninBEntry 11 27 := vasyuninBEntry_correct_axiom 11 27

theorem vasyuninBEntry_11_27_eval :
    ((((5244943/90570000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 27) ∧
    (vasyuninBEntry 11 27 ≤ (((5263057/90570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1127_formula_bound
  constructor <;> linarith

theorem G11_27_interval :
    ((((5244943/90570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 27) ∧
    (baezDuarteGramEntry 11 27 ≤ (((5263057/90570000) : ℚ) : ℝ)) := by
  rw [G11_27_formula]
  exact vasyuninBEntry_11_27_eval

def interval_11_27 : NamedVasyuninInterval :=
{
  h := 11
  k := 27
  lower := (5244943/90570000)
  upper := (5263057/90570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_27_interval
}

theorem G11_28_formula : baezDuarteGramEntry 11 28 = vasyuninBEntry 11 28 := vasyuninBEntry_correct_axiom 11 28

theorem vasyuninBEntry_11_28_eval :
    ((((48823551/864490000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 28) ∧
    (vasyuninBEntry 11 28 ≤ (((48996449/864490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1128_formula_bound
  constructor <;> linarith

theorem G11_28_interval :
    ((((48823551/864490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 28) ∧
    (baezDuarteGramEntry 11 28 ≤ (((48996449/864490000) : ℚ) : ℝ)) := by
  rw [G11_28_formula]
  exact vasyuninBEntry_11_28_eval

def interval_11_28 : NamedVasyuninInterval :=
{
  h := 11
  k := 28
  lower := (48823551/864490000)
  upper := (48996449/864490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_28_interval
}

theorem G11_29_formula : baezDuarteGramEntry 11 29 = vasyuninBEntry 11 29 := vasyuninBEntry_correct_axiom 11 29

theorem vasyuninBEntry_11_29_eval :
    ((((54900389/996110000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 29) ∧
    (vasyuninBEntry 11 29 ≤ (((55099611/996110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1129_formula_bound
  constructor <;> linarith

theorem G11_29_interval :
    ((((54900389/996110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 29) ∧
    (baezDuarteGramEntry 11 29 ≤ (((55099611/996110000) : ℚ) : ℝ)) := by
  rw [G11_29_formula]
  exact vasyuninBEntry_11_29_eval

def interval_11_29 : NamedVasyuninInterval :=
{
  h := 11
  k := 29
  lower := (54900389/996110000)
  upper := (55099611/996110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_29_interval
}

theorem G11_30_formula : baezDuarteGramEntry 11 30 = vasyuninBEntry 11 30 := vasyuninBEntry_correct_axiom 11 30

theorem vasyuninBEntry_11_30_eval :
    ((((19384071/359290000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 30) ∧
    (vasyuninBEntry 11 30 ≤ (((19455929/359290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1130_formula_bound
  constructor <;> linarith

theorem G11_30_interval :
    ((((19384071/359290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 30) ∧
    (baezDuarteGramEntry 11 30 ≤ (((19455929/359290000) : ℚ) : ℝ)) := by
  rw [G11_30_formula]
  exact vasyuninBEntry_11_30_eval

def interval_11_30 : NamedVasyuninInterval :=
{
  h := 11
  k := 30
  lower := (19384071/359290000)
  upper := (19455929/359290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_30_interval
}

theorem G11_31_formula : baezDuarteGramEntry 11 31 = vasyuninBEntry 11 31 := vasyuninBEntry_correct_axiom 11 31

theorem vasyuninBEntry_11_31_eval :
    ((((51792233/977670000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 31) ∧
    (vasyuninBEntry 11 31 ≤ (((51987767/977670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1131_formula_bound
  constructor <;> linarith

theorem G11_31_interval :
    ((((51792233/977670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 31) ∧
    (baezDuarteGramEntry 11 31 ≤ (((51987767/977670000) : ℚ) : ℝ)) := by
  rw [G11_31_formula]
  exact vasyuninBEntry_11_31_eval

def interval_11_31 : NamedVasyuninInterval :=
{
  h := 11
  k := 31
  lower := (51792233/977670000)
  upper := (51987767/977670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_31_interval
}

theorem G11_32_formula : baezDuarteGramEntry 11 32 = vasyuninBEntry 11 32 := vasyuninBEntry_correct_axiom 11 32

theorem vasyuninBEntry_11_32_eval :
    ((((23729591/454090000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 32) ∧
    (vasyuninBEntry 11 32 ≤ (((23820409/454090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1132_formula_bound
  constructor <;> linarith

theorem G11_32_interval :
    ((((23729591/454090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 32) ∧
    (baezDuarteGramEntry 11 32 ≤ (((23820409/454090000) : ℚ) : ℝ)) := by
  rw [G11_32_formula]
  exact vasyuninBEntry_11_32_eval

def interval_11_32 : NamedVasyuninInterval :=
{
  h := 11
  k := 32
  lower := (23729591/454090000)
  upper := (23820409/454090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_32_interval
}

theorem G11_33_formula : baezDuarteGramEntry 11 33 = vasyuninBEntry 11 33 := vasyuninBEntry_correct_axiom 11 33

theorem vasyuninBEntry_11_33_eval :
    ((((3752807/71930000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 33) ∧
    (vasyuninBEntry 11 33 ≤ (((3767193/71930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 11 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 11)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 11)
  constructor <;> linarith

theorem G11_33_interval :
    ((((3752807/71930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 33) ∧
    (baezDuarteGramEntry 11 33 ≤ (((3767193/71930000) : ℚ) : ℝ)) := by
  rw [G11_33_formula]
  exact vasyuninBEntry_11_33_eval

def interval_11_33 : NamedVasyuninInterval :=
{
  h := 11
  k := 33
  lower := (3752807/71930000)
  upper := (3767193/71930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_33_interval
}

theorem G11_34_formula : baezDuarteGramEntry 11 34 = vasyuninBEntry 11 34 := vasyuninBEntry_correct_axiom 11 34

theorem vasyuninBEntry_11_34_eval :
    ((((35030131/698690000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 34) ∧
    (vasyuninBEntry 11 34 ≤ (((35169869/698690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1134_formula_bound
  constructor <;> linarith

theorem G11_34_interval :
    ((((35030131/698690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 34) ∧
    (baezDuarteGramEntry 11 34 ≤ (((35169869/698690000) : ℚ) : ℝ)) := by
  rw [G11_34_formula]
  exact vasyuninBEntry_11_34_eval

def interval_11_34 : NamedVasyuninInterval :=
{
  h := 11
  k := 34
  lower := (35030131/698690000)
  upper := (35169869/698690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_34_interval
}

theorem G11_35_formula : baezDuarteGramEntry 11 35 = vasyuninBEntry 11 35 := vasyuninBEntry_correct_axiom 11 35

theorem vasyuninBEntry_11_35_eval :
    ((((46314997/950030000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 35) ∧
    (vasyuninBEntry 11 35 ≤ (((46505003/950030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1135_formula_bound
  constructor <;> linarith

theorem G11_35_interval :
    ((((46314997/950030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 35) ∧
    (baezDuarteGramEntry 11 35 ≤ (((46505003/950030000) : ℚ) : ℝ)) := by
  rw [G11_35_formula]
  exact vasyuninBEntry_11_35_eval

def interval_11_35 : NamedVasyuninInterval :=
{
  h := 11
  k := 35
  lower := (46314997/950030000)
  upper := (46505003/950030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_35_interval
}

theorem G11_36_formula : baezDuarteGramEntry 11 36 = vasyuninBEntry 11 36 := vasyuninBEntry_correct_axiom 11 36

theorem vasyuninBEntry_11_36_eval :
    ((((27252747/572530000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 36) ∧
    (vasyuninBEntry 11 36 ≤ (((27367253/572530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1136_formula_bound
  constructor <;> linarith

theorem G11_36_interval :
    ((((27252747/572530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 36) ∧
    (baezDuarteGramEntry 11 36 ≤ (((27367253/572530000) : ℚ) : ℝ)) := by
  rw [G11_36_formula]
  exact vasyuninBEntry_11_36_eval

def interval_11_36 : NamedVasyuninInterval :=
{
  h := 11
  k := 36
  lower := (27252747/572530000)
  upper := (27367253/572530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_36_interval
}

theorem G11_37_formula : baezDuarteGramEntry 11 37 = vasyuninBEntry 11 37 := vasyuninBEntry_correct_axiom 11 37

theorem vasyuninBEntry_11_37_eval :
    ((((41800289/897110000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 37) ∧
    (vasyuninBEntry 11 37 ≤ (((41979711/897110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1137_formula_bound
  constructor <;> linarith

theorem G11_37_interval :
    ((((41800289/897110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 37) ∧
    (baezDuarteGramEntry 11 37 ≤ (((41979711/897110000) : ℚ) : ℝ)) := by
  rw [G11_37_formula]
  exact vasyuninBEntry_11_37_eval

def interval_11_37 : NamedVasyuninInterval :=
{
  h := 11
  k := 37
  lower := (41800289/897110000)
  upper := (41979711/897110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_37_interval
}

theorem G11_38_formula : baezDuarteGramEntry 11 38 = vasyuninBEntry 11 38 := vasyuninBEntry_correct_axiom 11 38

theorem vasyuninBEntry_11_38_eval :
    ((((528843/11570000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 38) ∧
    (vasyuninBEntry 11 38 ≤ (((531157/11570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1138_formula_bound
  constructor <;> linarith

theorem G11_38_interval :
    ((((528843/11570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 38) ∧
    (baezDuarteGramEntry 11 38 ≤ (((531157/11570000) : ℚ) : ℝ)) := by
  rw [G11_38_formula]
  exact vasyuninBEntry_11_38_eval

def interval_11_38 : NamedVasyuninInterval :=
{
  h := 11
  k := 38
  lower := (528843/11570000)
  upper := (531157/11570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_38_interval
}

theorem G11_39_formula : baezDuarteGramEntry 11 39 = vasyuninBEntry 11 39 := vasyuninBEntry_correct_axiom 11 39

theorem vasyuninBEntry_11_39_eval :
    ((((41886633/933670000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 39) ∧
    (vasyuninBEntry 11 39 ≤ (((42073367/933670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1139_formula_bound
  constructor <;> linarith

theorem G11_39_interval :
    ((((41886633/933670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 39) ∧
    (baezDuarteGramEntry 11 39 ≤ (((42073367/933670000) : ℚ) : ℝ)) := by
  rw [G11_39_formula]
  exact vasyuninBEntry_11_39_eval

def interval_11_39 : NamedVasyuninInterval :=
{
  h := 11
  k := 39
  lower := (41886633/933670000)
  upper := (42073367/933670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_39_interval
}

theorem G11_40_formula : baezDuarteGramEntry 11 40 = vasyuninBEntry 11 40 := vasyuninBEntry_correct_axiom 11 40

theorem vasyuninBEntry_11_40_eval :
    ((((295569/6710000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 40) ∧
    (vasyuninBEntry 11 40 ≤ (((296911/6710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1140_formula_bound
  constructor <;> linarith

theorem G11_40_interval :
    ((((295569/6710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 40) ∧
    (baezDuarteGramEntry 11 40 ≤ (((296911/6710000) : ℚ) : ℝ)) := by
  rw [G11_40_formula]
  exact vasyuninBEntry_11_40_eval

def interval_11_40 : NamedVasyuninInterval :=
{
  h := 11
  k := 40
  lower := (295569/6710000)
  upper := (296911/6710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_40_interval
}

theorem G11_41_formula : baezDuarteGramEntry 11 41 = vasyuninBEntry 11 41 := vasyuninBEntry_correct_axiom 11 41

theorem vasyuninBEntry_11_41_eval :
    ((((6439141/148590000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 41) ∧
    (vasyuninBEntry 11 41 ≤ (((6468859/148590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1141_formula_bound
  constructor <;> linarith

theorem G11_41_interval :
    ((((6439141/148590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 41) ∧
    (baezDuarteGramEntry 11 41 ≤ (((6468859/148590000) : ℚ) : ℝ)) := by
  rw [G11_41_formula]
  exact vasyuninBEntry_11_41_eval

def interval_11_41 : NamedVasyuninInterval :=
{
  h := 11
  k := 41
  lower := (6439141/148590000)
  upper := (6468859/148590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_41_interval
}

theorem G11_42_formula : baezDuarteGramEntry 11 42 = vasyuninBEntry 11 42 := vasyuninBEntry_correct_axiom 11 42

theorem vasyuninBEntry_11_42_eval :
    ((((7747863/181370000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 42) ∧
    (vasyuninBEntry 11 42 ≤ (((7784137/181370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1142_formula_bound
  constructor <;> linarith

theorem G11_42_interval :
    ((((7747863/181370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 42) ∧
    (baezDuarteGramEntry 11 42 ≤ (((7784137/181370000) : ℚ) : ℝ)) := by
  rw [G11_42_formula]
  exact vasyuninBEntry_11_42_eval

def interval_11_42 : NamedVasyuninInterval :=
{
  h := 11
  k := 42
  lower := (7747863/181370000)
  upper := (7784137/181370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_42_interval
}

theorem G11_43_formula : baezDuarteGramEntry 11 43 = vasyuninBEntry 11 43 := vasyuninBEntry_correct_axiom 11 43

theorem vasyuninBEntry_11_43_eval :
    ((((13847219/327810000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 43) ∧
    (vasyuninBEntry 11 43 ≤ (((13912781/327810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1143_formula_bound
  constructor <;> linarith

theorem G11_43_interval :
    ((((13847219/327810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 43) ∧
    (baezDuarteGramEntry 11 43 ≤ (((13912781/327810000) : ℚ) : ℝ)) := by
  rw [G11_43_formula]
  exact vasyuninBEntry_11_43_eval

def interval_11_43 : NamedVasyuninInterval :=
{
  h := 11
  k := 43
  lower := (13847219/327810000)
  upper := (13912781/327810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_43_interval
}

theorem G11_44_formula : baezDuarteGramEntry 11 44 = vasyuninBEntry 11 44 := vasyuninBEntry_correct_axiom 11 44

theorem vasyuninBEntry_11_44_eval :
    ((((1596709/37910000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 44) ∧
    (vasyuninBEntry 11 44 ≤ (((1604291/37910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 11 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 11)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 11)
  constructor <;> linarith

theorem G11_44_interval :
    ((((1596709/37910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 44) ∧
    (baezDuarteGramEntry 11 44 ≤ (((1604291/37910000) : ℚ) : ℝ)) := by
  rw [G11_44_formula]
  exact vasyuninBEntry_11_44_eval

def interval_11_44 : NamedVasyuninInterval :=
{
  h := 11
  k := 44
  lower := (1596709/37910000)
  upper := (1604291/37910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_44_interval
}

theorem G11_45_formula : baezDuarteGramEntry 11 45 = vasyuninBEntry 11 45 := vasyuninBEntry_correct_axiom 11 45

theorem vasyuninBEntry_11_45_eval :
    ((((35273743/862570000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 45) ∧
    (vasyuninBEntry 11 45 ≤ (((35446257/862570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1145_formula_bound
  constructor <;> linarith

theorem G11_45_interval :
    ((((35273743/862570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 45) ∧
    (baezDuarteGramEntry 11 45 ≤ (((35446257/862570000) : ℚ) : ℝ)) := by
  rw [G11_45_formula]
  exact vasyuninBEntry_11_45_eval

def interval_11_45 : NamedVasyuninInterval :=
{
  h := 11
  k := 45
  lower := (35273743/862570000)
  upper := (35446257/862570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_45_interval
}

theorem G11_46_formula : baezDuarteGramEntry 11 46 = vasyuninBEntry 11 46 := vasyuninBEntry_correct_axiom 11 46

theorem vasyuninBEntry_11_46_eval :
    ((((2041151/50990000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 46) ∧
    (vasyuninBEntry 11 46 ≤ (((2051349/50990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1146_formula_bound
  constructor <;> linarith

theorem G11_46_interval :
    ((((2041151/50990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 46) ∧
    (baezDuarteGramEntry 11 46 ≤ (((2051349/50990000) : ℚ) : ℝ)) := by
  rw [G11_46_formula]
  exact vasyuninBEntry_11_46_eval

def interval_11_46 : NamedVasyuninInterval :=
{
  h := 11
  k := 46
  lower := (2041151/50990000)
  upper := (2051349/50990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_46_interval
}

theorem G11_47_formula : baezDuarteGramEntry 11 47 = vasyuninBEntry 11 47 := vasyuninBEntry_correct_axiom 11 47

theorem vasyuninBEntry_11_47_eval :
    ((((23689717/602830000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 47) ∧
    (vasyuninBEntry 11 47 ≤ (((23810283/602830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1147_formula_bound
  constructor <;> linarith

theorem G11_47_interval :
    ((((23689717/602830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 47) ∧
    (baezDuarteGramEntry 11 47 ≤ (((23810283/602830000) : ℚ) : ℝ)) := by
  rw [G11_47_formula]
  exact vasyuninBEntry_11_47_eval

def interval_11_47 : NamedVasyuninInterval :=
{
  h := 11
  k := 47
  lower := (23689717/602830000)
  upper := (23810283/602830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_47_interval
}

theorem G11_48_formula : baezDuarteGramEntry 11 48 = vasyuninBEntry 11 48 := vasyuninBEntry_correct_axiom 11 48

theorem vasyuninBEntry_11_48_eval :
    ((((13265673/343270000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 48) ∧
    (vasyuninBEntry 11 48 ≤ (((13334327/343270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1148_formula_bound
  constructor <;> linarith

theorem G11_48_interval :
    ((((13265673/343270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 48) ∧
    (baezDuarteGramEntry 11 48 ≤ (((13334327/343270000) : ℚ) : ℝ)) := by
  rw [G11_48_formula]
  exact vasyuninBEntry_11_48_eval

def interval_11_48 : NamedVasyuninInterval :=
{
  h := 11
  k := 48
  lower := (13265673/343270000)
  upper := (13334327/343270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_48_interval
}

theorem G11_49_formula : baezDuarteGramEntry 11 49 = vasyuninBEntry 11 49 := vasyuninBEntry_correct_axiom 11 49

theorem vasyuninBEntry_11_49_eval :
    ((((15274867/401330000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 49) ∧
    (vasyuninBEntry 11 49 ≤ (((15355133/401330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1149_formula_bound
  constructor <;> linarith

theorem G11_49_interval :
    ((((15274867/401330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 49) ∧
    (baezDuarteGramEntry 11 49 ≤ (((15355133/401330000) : ℚ) : ℝ)) := by
  rw [G11_49_formula]
  exact vasyuninBEntry_11_49_eval

def interval_11_49 : NamedVasyuninInterval :=
{
  h := 11
  k := 49
  lower := (15274867/401330000)
  upper := (15355133/401330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_49_interval
}

theorem G11_50_formula : baezDuarteGramEntry 11 50 = vasyuninBEntry 11 50 := vasyuninBEntry_correct_axiom 11 50

theorem vasyuninBEntry_11_50_eval :
    ((((36133637/963630000) : ℚ) : ℝ) ≤ vasyuninBEntry 11 50) ∧
    (vasyuninBEntry 11 50 ≤ (((36326363/963630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1150_formula_bound
  constructor <;> linarith

theorem G11_50_interval :
    ((((36133637/963630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 11 50) ∧
    (baezDuarteGramEntry 11 50 ≤ (((36326363/963630000) : ℚ) : ℝ)) := by
  rw [G11_50_formula]
  exact vasyuninBEntry_11_50_eval

def interval_11_50 : NamedVasyuninInterval :=
{
  h := 11
  k := 50
  lower := (36133637/963630000)
  upper := (36326363/963630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G11_50_interval
}

theorem G12_1_formula : baezDuarteGramEntry 12 1 = vasyuninBEntry 1 12 := by
  rw [baezDuarteGramEntry_symm 12 1]
  exact G1_12_formula

theorem G12_1_interval :
    ((((47665997/240030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 1) ∧
    (baezDuarteGramEntry 12 1 ≤ (((47714003/240030000) : ℚ) : ℝ)) := by
  rw [G12_1_formula]
  exact vasyuninBEntry_1_12_eval

def interval_12_1 : NamedVasyuninInterval :=
{
  h := 12
  k := 1
  lower := (47665997/240030000)
  upper := (47714003/240030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_1_interval
}

theorem G12_2_formula : baezDuarteGramEntry 12 2 = vasyuninBEntry 2 12 := by
  rw [baezDuarteGramEntry_symm 12 2]
  exact G2_12_formula

theorem G12_2_interval :
    ((((69074523/404770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 2) ∧
    (baezDuarteGramEntry 12 2 ≤ (((69155477/404770000) : ℚ) : ℝ)) := by
  rw [G12_2_formula]
  exact vasyuninBEntry_2_12_eval

def interval_12_2 : NamedVasyuninInterval :=
{
  h := 12
  k := 2
  lower := (69074523/404770000)
  upper := (69155477/404770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_2_interval
}

theorem G12_3_formula : baezDuarteGramEntry 12 3 = vasyuninBEntry 3 12 := by
  rw [baezDuarteGramEntry_symm 12 3]
  exact G3_12_formula

theorem G12_3_interval :
    ((((50607287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 3) ∧
    (baezDuarteGramEntry 12 3 ≤ (((50672713/327130000) : ℚ) : ℝ)) := by
  rw [G12_3_formula]
  exact vasyuninBEntry_3_12_eval

def interval_12_3 : NamedVasyuninInterval :=
{
  h := 12
  k := 3
  lower := (50607287/327130000)
  upper := (50672713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_3_interval
}

theorem G12_4_formula : baezDuarteGramEntry 12 4 = vasyuninBEntry 4 12 := by
  rw [baezDuarteGramEntry_symm 12 4]
  exact G4_12_formula

theorem G12_4_interval :
    ((((134556331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 4) ∧
    (baezDuarteGramEntry 12 4 ≤ (((134743669/936690000) : ℚ) : ℝ)) := by
  rw [G12_4_formula]
  exact vasyuninBEntry_4_12_eval

def interval_12_4 : NamedVasyuninInterval :=
{
  h := 12
  k := 4
  lower := (134556331/936690000)
  upper := (134743669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_4_interval
}

theorem G12_5_formula : baezDuarteGramEntry 12 5 = vasyuninBEntry 5 12 := by
  rw [baezDuarteGramEntry_symm 12 5]
  exact G5_12_formula

theorem G12_5_interval :
    ((((40823471/315290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 5) ∧
    (baezDuarteGramEntry 12 5 ≤ (((40886529/315290000) : ℚ) : ℝ)) := by
  rw [G12_5_formula]
  exact vasyuninBEntry_5_12_eval

def interval_12_5 : NamedVasyuninInterval :=
{
  h := 12
  k := 5
  lower := (40823471/315290000)
  upper := (40886529/315290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_5_interval
}

theorem G12_6_formula : baezDuarteGramEntry 12 6 = vasyuninBEntry 6 12 := by
  rw [baezDuarteGramEntry_symm 12 6]
  exact G6_12_formula

theorem G12_6_interval :
    ((((56760863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 6) ∧
    (baezDuarteGramEntry 12 6 ≤ (((56849137/441370000) : ℚ) : ℝ)) := by
  rw [G12_6_formula]
  exact vasyuninBEntry_6_12_eval

def interval_12_6 : NamedVasyuninInterval :=
{
  h := 12
  k := 6
  lower := (56760863/441370000)
  upper := (56849137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_6_interval
}

theorem G12_7_formula : baezDuarteGramEntry 12 7 = vasyuninBEntry 7 12 := by
  rw [baezDuarteGramEntry_symm 12 7]
  exact G7_12_formula

theorem G12_7_interval :
    ((((94797571/824290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 7) ∧
    (baezDuarteGramEntry 12 7 ≤ (((94962429/824290000) : ℚ) : ℝ)) := by
  rw [G12_7_formula]
  exact vasyuninBEntry_7_12_eval

def interval_12_7 : NamedVasyuninInterval :=
{
  h := 12
  k := 7
  lower := (94797571/824290000)
  upper := (94962429/824290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_7_interval
}

theorem G12_8_formula : baezDuarteGramEntry 12 8 = vasyuninBEntry 8 12 := by
  rw [baezDuarteGramEntry_symm 12 8]
  exact G8_12_formula

theorem G12_8_interval :
    ((((14656697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 8) ∧
    (baezDuarteGramEntry 12 8 ≤ (((14683303/133030000) : ℚ) : ℝ)) := by
  rw [G12_8_formula]
  exact vasyuninBEntry_8_12_eval

def interval_12_8 : NamedVasyuninInterval :=
{
  h := 12
  k := 8
  lower := (14656697/133030000)
  upper := (14683303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_8_interval
}

theorem G12_9_formula : baezDuarteGramEntry 12 9 = vasyuninBEntry 9 12 := by
  rw [baezDuarteGramEntry_symm 12 9]
  exact G9_12_formula

theorem G12_9_interval :
    ((((12627979/120210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 9) ∧
    (baezDuarteGramEntry 12 9 ≤ (((12652021/120210000) : ℚ) : ℝ)) := by
  rw [G12_9_formula]
  exact vasyuninBEntry_9_12_eval

def interval_12_9 : NamedVasyuninInterval :=
{
  h := 12
  k := 9
  lower := (12627979/120210000)
  upper := (12652021/120210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_9_interval
}

theorem G12_10_formula : baezDuarteGramEntry 12 10 = vasyuninBEntry 10 12 := by
  rw [baezDuarteGramEntry_symm 12 10]
  exact G10_12_formula

theorem G12_10_interval :
    ((((17482859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 10) ∧
    (baezDuarteGramEntry 12 10 ≤ (((17517141/171410000) : ℚ) : ℝ)) := by
  rw [G12_10_formula]
  exact vasyuninBEntry_10_12_eval

def interval_12_10 : NamedVasyuninInterval :=
{
  h := 12
  k := 10
  lower := (17482859/171410000)
  upper := (17517141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_10_interval
}

theorem G12_11_formula : baezDuarteGramEntry 12 11 = vasyuninBEntry 11 12 := by
  rw [baezDuarteGramEntry_symm 12 11]
  exact G11_12_formula

theorem G12_11_interval :
    ((((36858559/364410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 11) ∧
    (baezDuarteGramEntry 12 11 ≤ (((36931441/364410000) : ℚ) : ℝ)) := by
  rw [G12_11_formula]
  exact vasyuninBEntry_11_12_eval

def interval_12_11 : NamedVasyuninInterval :=
{
  h := 12
  k := 11
  lower := (36858559/364410000)
  upper := (36931441/364410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_11_interval
}

theorem G12_12_formula_eq : baezDuarteGramEntry 12 12 = (1 / (12 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 12 := by norm_num
  rw [baez_duarte_diagonal_scaling 12 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G12_12_log_gamma_interval :
  ((((99305383/946170000) : ℚ) : ℝ) ≤ (1 / (12 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (12 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((99494617/946170000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 12 (by norm_num)
  constructor
  · have : ((((99305383/946170000) : ℚ) : ℝ) ≤ (1 / (12 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (12 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((99494617/946170000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G12_12_interval : ((((99305383/946170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 12) ∧ (baezDuarteGramEntry 12 12 ≤ (((99494617/946170000) : ℚ) : ℝ)) := by
  rw [G12_12_formula_eq]
  exact G12_12_log_gamma_interval

def interval_12_12 : NamedVasyuninInterval :=
{
  h := 12
  k := 12
  lower := (99305383/946170000)
  upper := (99494617/946170000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G12_12_interval
}

theorem G12_13_formula : baezDuarteGramEntry 12 13 = vasyuninBEntry 12 13 := vasyuninBEntry_correct_axiom 12 13

theorem vasyuninBEntry_12_13_eval :
    ((((1308599/14010000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 13) ∧
    (vasyuninBEntry 12 13 ≤ (((1311401/14010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1213_formula_bound
  constructor <;> linarith

theorem G12_13_interval :
    ((((1308599/14010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 13) ∧
    (baezDuarteGramEntry 12 13 ≤ (((1311401/14010000) : ℚ) : ℝ)) := by
  rw [G12_13_formula]
  exact vasyuninBEntry_12_13_eval

def interval_12_13 : NamedVasyuninInterval :=
{
  h := 12
  k := 13
  lower := (1308599/14010000)
  upper := (1311401/14010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_13_interval
}

theorem G12_14_formula : baezDuarteGramEntry 12 14 = vasyuninBEntry 12 14 := vasyuninBEntry_correct_axiom 12 14

theorem vasyuninBEntry_12_14_eval :
    ((((40833059/469410000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 14) ∧
    (vasyuninBEntry 12 14 ≤ (((40926941/469410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 7 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G12_14_interval :
    ((((40833059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 14) ∧
    (baezDuarteGramEntry 12 14 ≤ (((40926941/469410000) : ℚ) : ℝ)) := by
  rw [G12_14_formula]
  exact vasyuninBEntry_12_14_eval

def interval_12_14 : NamedVasyuninInterval :=
{
  h := 12
  k := 14
  lower := (40833059/469410000)
  upper := (40926941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_14_interval
}

theorem G12_15_formula : baezDuarteGramEntry 12 15 = vasyuninBEntry 12 15 := vasyuninBEntry_correct_axiom 12 15

theorem vasyuninBEntry_12_15_eval :
    ((((62534071/759290000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 15) ∧
    (vasyuninBEntry 12 15 ≤ (((62685929/759290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G12_15_interval :
    ((((62534071/759290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 15) ∧
    (baezDuarteGramEntry 12 15 ≤ (((62685929/759290000) : ℚ) : ℝ)) := by
  rw [G12_15_formula]
  exact vasyuninBEntry_12_15_eval

def interval_12_15 : NamedVasyuninInterval :=
{
  h := 12
  k := 15
  lower := (62534071/759290000)
  upper := (62685929/759290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_15_interval
}

theorem G12_16_formula : baezDuarteGramEntry 12 16 = vasyuninBEntry 12 16 := vasyuninBEntry_correct_axiom 12 16

theorem vasyuninBEntry_12_16_eval :
    ((((3155993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 16) ∧
    (vasyuninBEntry 12 16 ≤ (((3164007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G12_16_interval :
    ((((3155993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 16) ∧
    (baezDuarteGramEntry 12 16 ≤ (((3164007/40070000) : ℚ) : ℝ)) := by
  rw [G12_16_formula]
  exact vasyuninBEntry_12_16_eval

def interval_12_16 : NamedVasyuninInterval :=
{
  h := 12
  k := 16
  lower := (3155993/40070000)
  upper := (3164007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_16_interval
}

theorem G12_17_formula : baezDuarteGramEntry 12 17 = vasyuninBEntry 12 17 := vasyuninBEntry_correct_axiom 12 17

theorem vasyuninBEntry_12_17_eval :
    ((((12688163/168370000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 17) ∧
    (vasyuninBEntry 12 17 ≤ (((12721837/168370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1217_formula_bound
  constructor <;> linarith

theorem G12_17_interval :
    ((((12688163/168370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 17) ∧
    (baezDuarteGramEntry 12 17 ≤ (((12721837/168370000) : ℚ) : ℝ)) := by
  rw [G12_17_formula]
  exact vasyuninBEntry_12_17_eval

def interval_12_17 : NamedVasyuninInterval :=
{
  h := 12
  k := 17
  lower := (12688163/168370000)
  upper := (12721837/168370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_17_interval
}

theorem G12_18_formula : baezDuarteGramEntry 12 18 = vasyuninBEntry 12 18 := vasyuninBEntry_correct_axiom 12 18

theorem vasyuninBEntry_12_18_eval :
    ((((9766697/133030000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 18) ∧
    (vasyuninBEntry 12 18 ≤ (((9793303/133030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G12_18_interval :
    ((((9766697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 18) ∧
    (baezDuarteGramEntry 12 18 ≤ (((9793303/133030000) : ℚ) : ℝ)) := by
  rw [G12_18_formula]
  exact vasyuninBEntry_12_18_eval

def interval_12_18 : NamedVasyuninInterval :=
{
  h := 12
  k := 18
  lower := (9766697/133030000)
  upper := (9793303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_18_interval
}

theorem G12_19_formula : baezDuarteGramEntry 12 19 = vasyuninBEntry 12 19 := vasyuninBEntry_correct_axiom 12 19

theorem vasyuninBEntry_12_19_eval :
    ((((2970771/42290000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 19) ∧
    (vasyuninBEntry 12 19 ≤ (((2979229/42290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1219_formula_bound
  constructor <;> linarith

theorem G12_19_interval :
    ((((2970771/42290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 19) ∧
    (baezDuarteGramEntry 12 19 ≤ (((2979229/42290000) : ℚ) : ℝ)) := by
  rw [G12_19_formula]
  exact vasyuninBEntry_12_19_eval

def interval_12_19 : NamedVasyuninInterval :=
{
  h := 12
  k := 19
  lower := (2970771/42290000)
  upper := (2979229/42290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_19_interval
}

theorem G12_20_formula : baezDuarteGramEntry 12 20 = vasyuninBEntry 12 20 := vasyuninBEntry_correct_axiom 12 20

theorem vasyuninBEntry_12_20_eval :
    ((((20140507/294930000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 20) ∧
    (vasyuninBEntry 12 20 ≤ (((20199493/294930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G12_20_interval :
    ((((20140507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 20) ∧
    (baezDuarteGramEntry 12 20 ≤ (((20199493/294930000) : ℚ) : ℝ)) := by
  rw [G12_20_formula]
  exact vasyuninBEntry_12_20_eval

def interval_12_20 : NamedVasyuninInterval :=
{
  h := 12
  k := 20
  lower := (20140507/294930000)
  upper := (20199493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_20_interval
}

theorem G12_21_formula : baezDuarteGramEntry 12 21 = vasyuninBEntry 12 21 := vasyuninBEntry_correct_axiom 12 21

theorem vasyuninBEntry_12_21_eval :
    ((((49345657/743430000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 21) ∧
    (vasyuninBEntry 12 21 ≤ (((49494343/743430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 7 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G12_21_interval :
    ((((49345657/743430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 21) ∧
    (baezDuarteGramEntry 12 21 ≤ (((49494343/743430000) : ℚ) : ℝ)) := by
  rw [G12_21_formula]
  exact vasyuninBEntry_12_21_eval

def interval_12_21 : NamedVasyuninInterval :=
{
  h := 12
  k := 21
  lower := (49345657/743430000)
  upper := (49494343/743430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_21_interval
}

theorem G12_22_formula : baezDuarteGramEntry 12 22 = vasyuninBEntry 12 22 := vasyuninBEntry_correct_axiom 12 22

theorem vasyuninBEntry_12_22_eval :
    ((((27931963/430370000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 22) ∧
    (vasyuninBEntry 12 22 ≤ (((28018037/430370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 11 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G12_22_interval :
    ((((27931963/430370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 22) ∧
    (baezDuarteGramEntry 12 22 ≤ (((28018037/430370000) : ℚ) : ℝ)) := by
  rw [G12_22_formula]
  exact vasyuninBEntry_12_22_eval

def interval_12_22 : NamedVasyuninInterval :=
{
  h := 12
  k := 22
  lower := (27931963/430370000)
  upper := (28018037/430370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_22_interval
}

theorem G12_23_formula : baezDuarteGramEntry 12 23 = vasyuninBEntry 12 23 := vasyuninBEntry_correct_axiom 12 23

theorem vasyuninBEntry_12_23_eval :
    ((((42833041/669590000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 23) ∧
    (vasyuninBEntry 12 23 ≤ (((42966959/669590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1223_formula_bound
  constructor <;> linarith

theorem G12_23_interval :
    ((((42833041/669590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 23) ∧
    (baezDuarteGramEntry 12 23 ≤ (((42966959/669590000) : ℚ) : ℝ)) := by
  rw [G12_23_formula]
  exact vasyuninBEntry_12_23_eval

def interval_12_23 : NamedVasyuninInterval :=
{
  h := 12
  k := 23
  lower := (42833041/669590000)
  upper := (42966959/669590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_23_interval
}

theorem G12_24_formula : baezDuarteGramEntry 12 24 = vasyuninBEntry 12 24 := vasyuninBEntry_correct_axiom 12 24

theorem vasyuninBEntry_12_24_eval :
    ((((14038151/218490000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 24) ∧
    (vasyuninBEntry 12 24 ≤ (((14081849/218490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 12 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 12)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 12)
  constructor <;> linarith

theorem G12_24_interval :
    ((((14038151/218490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 24) ∧
    (baezDuarteGramEntry 12 24 ≤ (((14081849/218490000) : ℚ) : ℝ)) := by
  rw [G12_24_formula]
  exact vasyuninBEntry_12_24_eval

def interval_12_24 : NamedVasyuninInterval :=
{
  h := 12
  k := 24
  lower := (14038151/218490000)
  upper := (14081849/218490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_24_interval
}

theorem G12_25_formula : baezDuarteGramEntry 12 25 = vasyuninBEntry 12 25 := vasyuninBEntry_correct_axiom 12 25

theorem vasyuninBEntry_12_25_eval :
    ((((32336729/532710000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 25) ∧
    (vasyuninBEntry 12 25 ≤ (((32443271/532710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1225_formula_bound
  constructor <;> linarith

theorem G12_25_interval :
    ((((32336729/532710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 25) ∧
    (baezDuarteGramEntry 12 25 ≤ (((32443271/532710000) : ℚ) : ℝ)) := by
  rw [G12_25_formula]
  exact vasyuninBEntry_12_25_eval

def interval_12_25 : NamedVasyuninInterval :=
{
  h := 12
  k := 25
  lower := (32336729/532710000)
  upper := (32443271/532710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_25_interval
}

theorem G12_26_formula : baezDuarteGramEntry 12 26 = vasyuninBEntry 12 26 := vasyuninBEntry_correct_axiom 12 26

theorem vasyuninBEntry_12_26_eval :
    ((((44563717/762830000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 26) ∧
    (vasyuninBEntry 12 26 ≤ (((44716283/762830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 13 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G12_26_interval :
    ((((44563717/762830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 26) ∧
    (baezDuarteGramEntry 12 26 ≤ (((44716283/762830000) : ℚ) : ℝ)) := by
  rw [G12_26_formula]
  exact vasyuninBEntry_12_26_eval

def interval_12_26 : NamedVasyuninInterval :=
{
  h := 12
  k := 26
  lower := (44563717/762830000)
  upper := (44716283/762830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_26_interval
}

theorem G12_27_formula : baezDuarteGramEntry 12 27 = vasyuninBEntry 12 27 := vasyuninBEntry_correct_axiom 12 27

theorem vasyuninBEntry_12_27_eval :
    ((((54284103/958970000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 27) ∧
    (vasyuninBEntry 12 27 ≤ (((54475897/958970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 9 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G12_27_interval :
    ((((54284103/958970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 27) ∧
    (baezDuarteGramEntry 12 27 ≤ (((54475897/958970000) : ℚ) : ℝ)) := by
  rw [G12_27_formula]
  exact vasyuninBEntry_12_27_eval

def interval_12_27 : NamedVasyuninInterval :=
{
  h := 12
  k := 27
  lower := (54284103/958970000)
  upper := (54475897/958970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_27_interval
}

theorem G12_28_formula : baezDuarteGramEntry 12 28 = vasyuninBEntry 12 28 := vasyuninBEntry_correct_axiom 12 28

theorem vasyuninBEntry_12_28_eval :
    ((((22289539/404610000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 28) ∧
    (vasyuninBEntry 12 28 ≤ (((22370461/404610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 7 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G12_28_interval :
    ((((22289539/404610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 28) ∧
    (baezDuarteGramEntry 12 28 ≤ (((22370461/404610000) : ℚ) : ℝ)) := by
  rw [G12_28_formula]
  exact vasyuninBEntry_12_28_eval

def interval_12_28 : NamedVasyuninInterval :=
{
  h := 12
  k := 28
  lower := (22289539/404610000)
  upper := (22370461/404610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_28_interval
}

theorem G12_29_formula : baezDuarteGramEntry 12 29 = vasyuninBEntry 12 29 := vasyuninBEntry_correct_axiom 12 29

theorem vasyuninBEntry_12_29_eval :
    ((((47351681/883190000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 29) ∧
    (vasyuninBEntry 12 29 ≤ (((47528319/883190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1229_formula_bound
  constructor <;> linarith

theorem G12_29_interval :
    ((((47351681/883190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 29) ∧
    (baezDuarteGramEntry 12 29 ≤ (((47528319/883190000) : ℚ) : ℝ)) := by
  rw [G12_29_formula]
  exact vasyuninBEntry_12_29_eval

def interval_12_29 : NamedVasyuninInterval :=
{
  h := 12
  k := 29
  lower := (47351681/883190000)
  upper := (47528319/883190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_29_interval
}

theorem G12_30_formula : baezDuarteGramEntry 12 30 = vasyuninBEntry 12 30 := vasyuninBEntry_correct_axiom 12 30

theorem vasyuninBEntry_12_30_eval :
    ((((6073461/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 30) ∧
    (vasyuninBEntry 12 30 ≤ (((6096539/115390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G12_30_interval :
    ((((6073461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 30) ∧
    (baezDuarteGramEntry 12 30 ≤ (((6096539/115390000) : ℚ) : ℝ)) := by
  rw [G12_30_formula]
  exact vasyuninBEntry_12_30_eval

def interval_12_30 : NamedVasyuninInterval :=
{
  h := 12
  k := 30
  lower := (6073461/115390000)
  upper := (6096539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_30_interval
}

theorem G12_31_formula : baezDuarteGramEntry 12 31 = vasyuninBEntry 12 31 := vasyuninBEntry_correct_axiom 12 31

theorem vasyuninBEntry_12_31_eval :
    ((((21053881/411190000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 31) ∧
    (vasyuninBEntry 12 31 ≤ (((21136119/411190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1231_formula_bound
  constructor <;> linarith

theorem G12_31_interval :
    ((((21053881/411190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 31) ∧
    (baezDuarteGramEntry 12 31 ≤ (((21136119/411190000) : ℚ) : ℝ)) := by
  rw [G12_31_formula]
  exact vasyuninBEntry_12_31_eval

def interval_12_31 : NamedVasyuninInterval :=
{
  h := 12
  k := 31
  lower := (21053881/411190000)
  upper := (21136119/411190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_31_interval
}

theorem G12_32_formula : baezDuarteGramEntry 12 32 = vasyuninBEntry 12 32 := vasyuninBEntry_correct_axiom 12 32

theorem vasyuninBEntry_12_32_eval :
    ((((48912587/974130000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 32) ∧
    (vasyuninBEntry 12 32 ≤ (((49107413/974130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 8 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G12_32_interval :
    ((((48912587/974130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 32) ∧
    (baezDuarteGramEntry 12 32 ≤ (((49107413/974130000) : ℚ) : ℝ)) := by
  rw [G12_32_formula]
  exact vasyuninBEntry_12_32_eval

def interval_12_32 : NamedVasyuninInterval :=
{
  h := 12
  k := 32
  lower := (48912587/974130000)
  upper := (49107413/974130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_32_interval
}

theorem G12_33_formula : baezDuarteGramEntry 12 33 = vasyuninBEntry 12 33 := vasyuninBEntry_correct_axiom 12 33

theorem vasyuninBEntry_12_33_eval :
    ((((19106193/388070000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 33) ∧
    (vasyuninBEntry 12 33 ≤ (((19183807/388070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 11 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G12_33_interval :
    ((((19106193/388070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 33) ∧
    (baezDuarteGramEntry 12 33 ≤ (((19183807/388070000) : ℚ) : ℝ)) := by
  rw [G12_33_formula]
  exact vasyuninBEntry_12_33_eval

def interval_12_33 : NamedVasyuninInterval :=
{
  h := 12
  k := 33
  lower := (19106193/388070000)
  upper := (19183807/388070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_33_interval
}

theorem G12_34_formula : baezDuarteGramEntry 12 34 = vasyuninBEntry 12 34 := vasyuninBEntry_correct_axiom 12 34

theorem vasyuninBEntry_12_34_eval :
    ((((8864197/183030000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 34) ∧
    (vasyuninBEntry 12 34 ≤ (((8900803/183030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 17 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G12_34_interval :
    ((((8864197/183030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 34) ∧
    (baezDuarteGramEntry 12 34 ≤ (((8900803/183030000) : ℚ) : ℝ)) := by
  rw [G12_34_formula]
  exact vasyuninBEntry_12_34_eval

def interval_12_34 : NamedVasyuninInterval :=
{
  h := 12
  k := 34
  lower := (8864197/183030000)
  upper := (8900803/183030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_34_interval
}

theorem G12_35_formula : baezDuarteGramEntry 12 35 = vasyuninBEntry 12 35 := vasyuninBEntry_correct_axiom 12 35

theorem vasyuninBEntry_12_35_eval :
    ((((4024091/84090000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 35) ∧
    (vasyuninBEntry 12 35 ≤ (((4040909/84090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1235_formula_bound
  constructor <;> linarith

theorem G12_35_interval :
    ((((4024091/84090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 35) ∧
    (baezDuarteGramEntry 12 35 ≤ (((4040909/84090000) : ℚ) : ℝ)) := by
  rw [G12_35_formula]
  exact vasyuninBEntry_12_35_eval

def interval_12_35 : NamedVasyuninInterval :=
{
  h := 12
  k := 35
  lower := (4024091/84090000)
  upper := (4040909/84090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_35_interval
}

theorem G12_36_formula : baezDuarteGramEntry 12 36 = vasyuninBEntry 12 36 := vasyuninBEntry_correct_axiom 12 36

theorem vasyuninBEntry_12_36_eval :
    ((((37910717/792830000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 36) ∧
    (vasyuninBEntry 12 36 ≤ (((38069283/792830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 12 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 12)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 12)
  constructor <;> linarith

theorem G12_36_interval :
    ((((37910717/792830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 36) ∧
    (baezDuarteGramEntry 12 36 ≤ (((38069283/792830000) : ℚ) : ℝ)) := by
  rw [G12_36_formula]
  exact vasyuninBEntry_12_36_eval

def interval_12_36 : NamedVasyuninInterval :=
{
  h := 12
  k := 36
  lower := (37910717/792830000)
  upper := (38069283/792830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_36_interval
}

theorem G12_37_formula : baezDuarteGramEntry 12 37 = vasyuninBEntry 12 37 := vasyuninBEntry_correct_axiom 12 37

theorem vasyuninBEntry_12_37_eval :
    ((((16623917/360830000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 37) ∧
    (vasyuninBEntry 12 37 ≤ (((16696083/360830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1237_formula_bound
  constructor <;> linarith

theorem G12_37_interval :
    ((((16623917/360830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 37) ∧
    (baezDuarteGramEntry 12 37 ≤ (((16696083/360830000) : ℚ) : ℝ)) := by
  rw [G12_37_formula]
  exact vasyuninBEntry_12_37_eval

def interval_12_37 : NamedVasyuninInterval :=
{
  h := 12
  k := 37
  lower := (16623917/360830000)
  upper := (16696083/360830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_37_interval
}

theorem G12_38_formula : baezDuarteGramEntry 12 38 = vasyuninBEntry 12 38 := vasyuninBEntry_correct_axiom 12 38

theorem vasyuninBEntry_12_38_eval :
    ((((8236647/183530000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 38) ∧
    (vasyuninBEntry 12 38 ≤ (((8273353/183530000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G12_38_interval :
    ((((8236647/183530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 38) ∧
    (baezDuarteGramEntry 12 38 ≤ (((8273353/183530000) : ℚ) : ℝ)) := by
  rw [G12_38_formula]
  exact vasyuninBEntry_12_38_eval

def interval_12_38 : NamedVasyuninInterval :=
{
  h := 12
  k := 38
  lower := (8236647/183530000)
  upper := (8273353/183530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_38_interval
}

theorem G12_39_formula : baezDuarteGramEntry 12 39 = vasyuninBEntry 12 39 := vasyuninBEntry_correct_axiom 12 39

theorem vasyuninBEntry_12_39_eval :
    ((((35309559/804410000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 39) ∧
    (vasyuninBEntry 12 39 ≤ (((35470441/804410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 13 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G12_39_interval :
    ((((35309559/804410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 39) ∧
    (baezDuarteGramEntry 12 39 ≤ (((35470441/804410000) : ℚ) : ℝ)) := by
  rw [G12_39_formula]
  exact vasyuninBEntry_12_39_eval

def interval_12_39 : NamedVasyuninInterval :=
{
  h := 12
  k := 39
  lower := (35309559/804410000)
  upper := (35470441/804410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_39_interval
}

theorem G12_40_formula : baezDuarteGramEntry 12 40 = vasyuninBEntry 12 40 := vasyuninBEntry_correct_axiom 12 40

theorem vasyuninBEntry_12_40_eval :
    ((((37014009/859910000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 40) ∧
    (vasyuninBEntry 12 40 ≤ (((37185991/859910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 10 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G12_40_interval :
    ((((37014009/859910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 40) ∧
    (baezDuarteGramEntry 12 40 ≤ (((37185991/859910000) : ℚ) : ℝ)) := by
  rw [G12_40_formula]
  exact vasyuninBEntry_12_40_eval

def interval_12_40 : NamedVasyuninInterval :=
{
  h := 12
  k := 40
  lower := (37014009/859910000)
  upper := (37185991/859910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_40_interval
}

theorem G12_41_formula : baezDuarteGramEntry 12 41 = vasyuninBEntry 12 41 := vasyuninBEntry_correct_axiom 12 41

theorem vasyuninBEntry_12_41_eval :
    ((((892261/21140000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 41) ∧
    (vasyuninBEntry 12 41 ≤ (((896489/21140000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1241_formula_bound
  constructor <;> linarith

theorem G12_41_interval :
    ((((892261/21140000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 41) ∧
    (baezDuarteGramEntry 12 41 ≤ (((896489/21140000) : ℚ) : ℝ)) := by
  rw [G12_41_formula]
  exact vasyuninBEntry_12_41_eval

def interval_12_41 : NamedVasyuninInterval :=
{
  h := 12
  k := 41
  lower := (892261/21140000)
  upper := (896489/21140000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_41_interval
}

theorem G12_42_formula : baezDuarteGramEntry 12 42 = vasyuninBEntry 12 42 := vasyuninBEntry_correct_axiom 12 42

theorem vasyuninBEntry_12_42_eval :
    ((((38088471/915290000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 42) ∧
    (vasyuninBEntry 12 42 ≤ (((38271529/915290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 7 6 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G12_42_interval :
    ((((38088471/915290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 42) ∧
    (baezDuarteGramEntry 12 42 ≤ (((38271529/915290000) : ℚ) : ℝ)) := by
  rw [G12_42_formula]
  exact vasyuninBEntry_12_42_eval

def interval_12_42 : NamedVasyuninInterval :=
{
  h := 12
  k := 42
  lower := (38088471/915290000)
  upper := (38271529/915290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_42_interval
}

theorem G12_43_formula : baezDuarteGramEntry 12 43 = vasyuninBEntry 12 43 := vasyuninBEntry_correct_axiom 12 43

theorem vasyuninBEntry_12_43_eval :
    ((((7595377/186230000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 43) ∧
    (vasyuninBEntry 12 43 ≤ (((7632623/186230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1243_formula_bound
  constructor <;> linarith

theorem G12_43_interval :
    ((((7595377/186230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 43) ∧
    (baezDuarteGramEntry 12 43 ≤ (((7632623/186230000) : ℚ) : ℝ)) := by
  rw [G12_43_formula]
  exact vasyuninBEntry_12_43_eval

def interval_12_43 : NamedVasyuninInterval :=
{
  h := 12
  k := 43
  lower := (7595377/186230000)
  upper := (7632623/186230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_43_interval
}

theorem G12_44_formula : baezDuarteGramEntry 12 44 = vasyuninBEntry 12 44 := vasyuninBEntry_correct_axiom 12 44

theorem vasyuninBEntry_12_44_eval :
    ((((18538861/461390000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 44) ∧
    (vasyuninBEntry 12 44 ≤ (((18631139/461390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 11 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G12_44_interval :
    ((((18538861/461390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 44) ∧
    (baezDuarteGramEntry 12 44 ≤ (((18631139/461390000) : ℚ) : ℝ)) := by
  rw [G12_44_formula]
  exact vasyuninBEntry_12_44_eval

def interval_12_44 : NamedVasyuninInterval :=
{
  h := 12
  k := 44
  lower := (18538861/461390000)
  upper := (18631139/461390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_44_interval
}

theorem G12_45_formula : baezDuarteGramEntry 12 45 = vasyuninBEntry 12 45 := vasyuninBEntry_correct_axiom 12 45

theorem vasyuninBEntry_12_45_eval :
    ((((24099113/608870000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 45) ∧
    (vasyuninBEntry 12 45 ≤ (((24220887/608870000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 15 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G12_45_interval :
    ((((24099113/608870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 45) ∧
    (baezDuarteGramEntry 12 45 ≤ (((24220887/608870000) : ℚ) : ℝ)) := by
  rw [G12_45_formula]
  exact vasyuninBEntry_12_45_eval

def interval_12_45 : NamedVasyuninInterval :=
{
  h := 12
  k := 45
  lower := (24099113/608870000)
  upper := (24220887/608870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_45_interval
}

theorem G12_46_formula : baezDuarteGramEntry 12 46 = vasyuninBEntry 12 46 := vasyuninBEntry_correct_axiom 12 46

theorem vasyuninBEntry_12_46_eval :
    ((((3750401/95990000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 46) ∧
    (vasyuninBEntry 12 46 ≤ (((3769599/95990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G12_46_interval :
    ((((3750401/95990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 46) ∧
    (baezDuarteGramEntry 12 46 ≤ (((3769599/95990000) : ℚ) : ℝ)) := by
  rw [G12_46_formula]
  exact vasyuninBEntry_12_46_eval

def interval_12_46 : NamedVasyuninInterval :=
{
  h := 12
  k := 46
  lower := (3750401/95990000)
  upper := (3769599/95990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_46_interval
}

theorem G12_47_formula : baezDuarteGramEntry 12 47 = vasyuninBEntry 12 47 := vasyuninBEntry_correct_axiom 12 47

theorem vasyuninBEntry_12_47_eval :
    ((((35647851/921490000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 47) ∧
    (vasyuninBEntry 12 47 ≤ (((35832149/921490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1247_formula_bound
  constructor <;> linarith

theorem G12_47_interval :
    ((((35647851/921490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 47) ∧
    (baezDuarteGramEntry 12 47 ≤ (((35832149/921490000) : ℚ) : ℝ)) := by
  rw [G12_47_formula]
  exact vasyuninBEntry_12_47_eval

def interval_12_47 : NamedVasyuninInterval :=
{
  h := 12
  k := 47
  lower := (35647851/921490000)
  upper := (35832149/921490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_47_interval
}

theorem G12_48_formula : baezDuarteGramEntry 12 48 = vasyuninBEntry 12 48 := vasyuninBEntry_correct_axiom 12 48

theorem vasyuninBEntry_12_48_eval :
    ((((12627287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 48) ∧
    (vasyuninBEntry 12 48 ≤ (((12692713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 12 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 12)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 12)
  constructor <;> linarith

theorem G12_48_interval :
    ((((12627287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 48) ∧
    (baezDuarteGramEntry 12 48 ≤ (((12692713/327130000) : ℚ) : ℝ)) := by
  rw [G12_48_formula]
  exact vasyuninBEntry_12_48_eval

def interval_12_48 : NamedVasyuninInterval :=
{
  h := 12
  k := 48
  lower := (12627287/327130000)
  upper := (12692713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_48_interval
}

theorem G12_49_formula : baezDuarteGramEntry 12 49 = vasyuninBEntry 12 49 := vasyuninBEntry_correct_axiom 12 49

theorem vasyuninBEntry_12_49_eval :
    ((((4419481/117690000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 49) ∧
    (vasyuninBEntry 12 49 ≤ (((4443019/117690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1249_formula_bound
  constructor <;> linarith

theorem G12_49_interval :
    ((((4419481/117690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 49) ∧
    (baezDuarteGramEntry 12 49 ≤ (((4443019/117690000) : ℚ) : ℝ)) := by
  rw [G12_49_formula]
  exact vasyuninBEntry_12_49_eval

def interval_12_49 : NamedVasyuninInterval :=
{
  h := 12
  k := 49
  lower := (4419481/117690000)
  upper := (4443019/117690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_49_interval
}

theorem G12_50_formula : baezDuarteGramEntry 12 50 = vasyuninBEntry 12 50 := vasyuninBEntry_correct_axiom 12 50

theorem vasyuninBEntry_12_50_eval :
    ((((3649087/99130000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 50) ∧
    (vasyuninBEntry 12 50 ≤ (((3668913/99130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G12_50_interval :
    ((((3649087/99130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 12 50) ∧
    (baezDuarteGramEntry 12 50 ≤ (((3668913/99130000) : ℚ) : ℝ)) := by
  rw [G12_50_formula]
  exact vasyuninBEntry_12_50_eval

def interval_12_50 : NamedVasyuninInterval :=
{
  h := 12
  k := 50
  lower := (3649087/99130000)
  upper := (3668913/99130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G12_50_interval
}

theorem G13_1_formula : baezDuarteGramEntry 13 1 = vasyuninBEntry 1 13 := by
  rw [baezDuarteGramEntry_symm 13 1]
  exact G1_13_formula

theorem G13_1_interval :
    ((((53581241/287590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 1) ∧
    (baezDuarteGramEntry 13 1 ≤ (((53638759/287590000) : ℚ) : ℝ)) := by
  rw [G13_1_formula]
  exact vasyuninBEntry_1_13_eval

def interval_13_1 : NamedVasyuninInterval :=
{
  h := 13
  k := 1
  lower := (53581241/287590000)
  upper := (53638759/287590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_1_interval
}

theorem G13_2_formula : baezDuarteGramEntry 13 2 = vasyuninBEntry 2 13 := by
  rw [baezDuarteGramEntry_symm 13 2]
  exact G2_13_formula

theorem G13_2_interval :
    ((((104703999/660010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 2) ∧
    (baezDuarteGramEntry 13 2 ≤ (((104836001/660010000) : ℚ) : ℝ)) := by
  rw [G13_2_formula]
  exact vasyuninBEntry_2_13_eval

def interval_13_2 : NamedVasyuninInterval :=
{
  h := 13
  k := 2
  lower := (104703999/660010000)
  upper := (104836001/660010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_2_interval
}

theorem G13_3_formula : baezDuarteGramEntry 13 3 = vasyuninBEntry 3 13 := by
  rw [baezDuarteGramEntry_symm 13 3]
  exact G3_13_formula

theorem G13_3_interval :
    ((((50979311/356890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 3) ∧
    (baezDuarteGramEntry 13 3 ≤ (((51050689/356890000) : ℚ) : ℝ)) := by
  rw [G13_3_formula]
  exact vasyuninBEntry_3_13_eval

def interval_13_3 : NamedVasyuninInterval :=
{
  h := 13
  k := 3
  lower := (50979311/356890000)
  upper := (51050689/356890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_3_interval
}

theorem G13_4_formula : baezDuarteGramEntry 13 4 = vasyuninBEntry 4 13 := by
  rw [baezDuarteGramEntry_symm 13 4]
  exact G4_13_formula

theorem G13_4_interval :
    ((((4026447/30530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 4) ∧
    (baezDuarteGramEntry 13 4 ≤ (((4032553/30530000) : ℚ) : ℝ)) := by
  rw [G13_4_formula]
  exact vasyuninBEntry_4_13_eval

def interval_13_4 : NamedVasyuninInterval :=
{
  h := 13
  k := 4
  lower := (4026447/30530000)
  upper := (4032553/30530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_4_interval
}

theorem G13_5_formula : baezDuarteGramEntry 13 5 = vasyuninBEntry 5 13 := by
  rw [baezDuarteGramEntry_symm 13 5]
  exact G5_13_formula

theorem G13_5_interval :
    ((((114946181/938190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 5) ∧
    (baezDuarteGramEntry 13 5 ≤ (((115133819/938190000) : ℚ) : ℝ)) := by
  rw [G13_5_formula]
  exact vasyuninBEntry_5_13_eval

def interval_13_5 : NamedVasyuninInterval :=
{
  h := 13
  k := 5
  lower := (114946181/938190000)
  upper := (115133819/938190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_5_interval
}

theorem G13_6_formula : baezDuarteGramEntry 13 6 = vasyuninBEntry 6 13 := by
  rw [baezDuarteGramEntry_symm 13 6]
  exact G6_13_formula

theorem G13_6_interval :
    ((((12443359/106410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 6) ∧
    (baezDuarteGramEntry 13 6 ≤ (((12464641/106410000) : ℚ) : ℝ)) := by
  rw [G13_6_formula]
  exact vasyuninBEntry_6_13_eval

def interval_13_6 : NamedVasyuninInterval :=
{
  h := 13
  k := 6
  lower := (12443359/106410000)
  upper := (12464641/106410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_6_interval
}

theorem G13_7_formula : baezDuarteGramEntry 13 7 = vasyuninBEntry 7 13 := by
  rw [baezDuarteGramEntry_symm 13 7]
  exact G7_13_formula

theorem G13_7_interval :
    ((((13636439/123110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 7) ∧
    (baezDuarteGramEntry 13 7 ≤ (((13661061/123110000) : ℚ) : ℝ)) := by
  rw [G13_7_formula]
  exact vasyuninBEntry_7_13_eval

def interval_13_7 : NamedVasyuninInterval :=
{
  h := 13
  k := 7
  lower := (13636439/123110000)
  upper := (13661061/123110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_7_interval
}

theorem G13_8_formula : baezDuarteGramEntry 13 8 = vasyuninBEntry 8 13 := by
  rw [baezDuarteGramEntry_symm 13 8]
  exact G8_13_formula

theorem G13_8_interval :
    ((((9109969/87810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 8) ∧
    (baezDuarteGramEntry 13 8 ≤ (((9127531/87810000) : ℚ) : ℝ)) := by
  rw [G13_8_formula]
  exact vasyuninBEntry_8_13_eval

def interval_13_8 : NamedVasyuninInterval :=
{
  h := 13
  k := 8
  lower := (9109969/87810000)
  upper := (9127531/87810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_8_interval
}

theorem G13_9_formula : baezDuarteGramEntry 13 9 = vasyuninBEntry 9 13 := by
  rw [baezDuarteGramEntry_symm 13 9]
  exact G9_13_formula

theorem G13_9_interval :
    ((((16962929/170710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 9) ∧
    (baezDuarteGramEntry 13 9 ≤ (((16997071/170710000) : ℚ) : ℝ)) := by
  rw [G13_9_formula]
  exact vasyuninBEntry_9_13_eval

def interval_13_9 : NamedVasyuninInterval :=
{
  h := 13
  k := 9
  lower := (16962929/170710000)
  upper := (16997071/170710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_9_interval
}

theorem G13_10_formula : baezDuarteGramEntry 13 10 = vasyuninBEntry 10 13 := by
  rw [baezDuarteGramEntry_symm 13 10]
  exact G10_13_formula

theorem G13_10_interval :
    ((((22993523/239770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 10) ∧
    (baezDuarteGramEntry 13 10 ≤ (((23041477/239770000) : ℚ) : ℝ)) := by
  rw [G13_10_formula]
  exact vasyuninBEntry_10_13_eval

def interval_13_10 : NamedVasyuninInterval :=
{
  h := 13
  k := 10
  lower := (22993523/239770000)
  upper := (23041477/239770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_10_interval
}

theorem G13_11_formula : baezDuarteGramEntry 13 11 = vasyuninBEntry 11 13 := by
  rw [baezDuarteGramEntry_symm 13 11]
  exact G11_13_formula

theorem G13_11_interval :
    ((((27340857/291430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 11) ∧
    (baezDuarteGramEntry 13 11 ≤ (((27399143/291430000) : ℚ) : ℝ)) := by
  rw [G13_11_formula]
  exact vasyuninBEntry_11_13_eval

def interval_13_11 : NamedVasyuninInterval :=
{
  h := 13
  k := 11
  lower := (27340857/291430000)
  upper := (27399143/291430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_11_interval
}

theorem G13_12_formula : baezDuarteGramEntry 13 12 = vasyuninBEntry 12 13 := by
  rw [baezDuarteGramEntry_symm 13 12]
  exact G12_13_formula

theorem G13_12_interval :
    ((((1308599/14010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 12) ∧
    (baezDuarteGramEntry 13 12 ≤ (((1311401/14010000) : ℚ) : ℝ)) := by
  rw [G13_12_formula]
  exact vasyuninBEntry_12_13_eval

def interval_13_12 : NamedVasyuninInterval :=
{
  h := 13
  k := 12
  lower := (1308599/14010000)
  upper := (1311401/14010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_12_interval
}

theorem G13_13_formula_eq : baezDuarteGramEntry 13 13 = (1 / (13 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 13 := by norm_num
  rw [baez_duarte_diagonal_scaling 13 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G13_13_log_gamma_interval :
  ((((67580239/697610000) : ℚ) : ℝ) ≤ (1 / (13 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (13 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((67719761/697610000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 13 (by norm_num)
  constructor
  · have : ((((67580239/697610000) : ℚ) : ℝ) ≤ (1 / (13 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (13 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((67719761/697610000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G13_13_interval : ((((67580239/697610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 13) ∧ (baezDuarteGramEntry 13 13 ≤ (((67719761/697610000) : ℚ) : ℝ)) := by
  rw [G13_13_formula_eq]
  exact G13_13_log_gamma_interval

def interval_13_13 : NamedVasyuninInterval :=
{
  h := 13
  k := 13
  lower := (67580239/697610000)
  upper := (67719761/697610000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G13_13_interval
}

theorem G13_14_formula : baezDuarteGramEntry 13 14 = vasyuninBEntry 13 14 := vasyuninBEntry_correct_axiom 13 14

theorem vasyuninBEntry_13_14_eval :
    ((((80816869/931310000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 14) ∧
    (vasyuninBEntry 13 14 ≤ (((81003131/931310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1314_formula_bound
  constructor <;> linarith

theorem G13_14_interval :
    ((((80816869/931310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 14) ∧
    (baezDuarteGramEntry 13 14 ≤ (((81003131/931310000) : ℚ) : ℝ)) := by
  rw [G13_14_formula]
  exact vasyuninBEntry_13_14_eval

def interval_13_14 : NamedVasyuninInterval :=
{
  h := 13
  k := 14
  lower := (80816869/931310000)
  upper := (81003131/931310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_14_interval
}

theorem G13_15_formula : baezDuarteGramEntry 13 15 = vasyuninBEntry 13 15 := vasyuninBEntry_correct_axiom 13 15

theorem vasyuninBEntry_13_15_eval :
    ((((26002911/320890000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 15) ∧
    (vasyuninBEntry 13 15 ≤ (((26067089/320890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1315_formula_bound
  constructor <;> linarith

theorem G13_15_interval :
    ((((26002911/320890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 15) ∧
    (baezDuarteGramEntry 13 15 ≤ (((26067089/320890000) : ℚ) : ℝ)) := by
  rw [G13_15_formula]
  exact vasyuninBEntry_13_15_eval

def interval_13_15 : NamedVasyuninInterval :=
{
  h := 13
  k := 15
  lower := (26002911/320890000)
  upper := (26067089/320890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_15_interval
}

theorem G13_16_formula : baezDuarteGramEntry 13 16 = vasyuninBEntry 13 16 := vasyuninBEntry_correct_axiom 13 16

theorem vasyuninBEntry_13_16_eval :
    ((((4146601/53990000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 16) ∧
    (vasyuninBEntry 13 16 ≤ (((4157399/53990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1316_formula_bound
  constructor <;> linarith

theorem G13_16_interval :
    ((((4146601/53990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 16) ∧
    (baezDuarteGramEntry 13 16 ≤ (((4157399/53990000) : ℚ) : ℝ)) := by
  rw [G13_16_formula]
  exact vasyuninBEntry_13_16_eval

def interval_13_16 : NamedVasyuninInterval :=
{
  h := 13
  k := 16
  lower := (4146601/53990000)
  upper := (4157399/53990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_16_interval
}

theorem G13_17_formula : baezDuarteGramEntry 13 17 = vasyuninBEntry 13 17 := vasyuninBEntry_correct_axiom 13 17

theorem vasyuninBEntry_13_17_eval :
    ((((22654157/308430000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 17) ∧
    (vasyuninBEntry 13 17 ≤ (((22715843/308430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1317_formula_bound
  constructor <;> linarith

theorem G13_17_interval :
    ((((22654157/308430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 17) ∧
    (baezDuarteGramEntry 13 17 ≤ (((22715843/308430000) : ℚ) : ℝ)) := by
  rw [G13_17_formula]
  exact vasyuninBEntry_13_17_eval

def interval_13_17 : NamedVasyuninInterval :=
{
  h := 13
  k := 17
  lower := (22654157/308430000)
  upper := (22715843/308430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_17_interval
}

theorem G13_18_formula : baezDuarteGramEntry 13 18 = vasyuninBEntry 13 18 := vasyuninBEntry_correct_axiom 13 18

theorem vasyuninBEntry_13_18_eval :
    ((((27021719/382810000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 18) ∧
    (vasyuninBEntry 13 18 ≤ (((27098281/382810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1318_formula_bound
  constructor <;> linarith

theorem G13_18_interval :
    ((((27021719/382810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 18) ∧
    (baezDuarteGramEntry 13 18 ≤ (((27098281/382810000) : ℚ) : ℝ)) := by
  rw [G13_18_formula]
  exact vasyuninBEntry_13_18_eval

def interval_13_18 : NamedVasyuninInterval :=
{
  h := 13
  k := 18
  lower := (27021719/382810000)
  upper := (27098281/382810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_18_interval
}

theorem G13_19_formula : baezDuarteGramEntry 13 19 = vasyuninBEntry 13 19 := vasyuninBEntry_correct_axiom 13 19

theorem vasyuninBEntry_13_19_eval :
    ((((18522891/271090000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 19) ∧
    (vasyuninBEntry 13 19 ≤ (((18577109/271090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1319_formula_bound
  constructor <;> linarith

theorem G13_19_interval :
    ((((18522891/271090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 19) ∧
    (baezDuarteGramEntry 13 19 ≤ (((18577109/271090000) : ℚ) : ℝ)) := by
  rw [G13_19_formula]
  exact vasyuninBEntry_13_19_eval

def interval_13_19 : NamedVasyuninInterval :=
{
  h := 13
  k := 19
  lower := (18522891/271090000)
  upper := (18577109/271090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_19_interval
}

theorem G13_20_formula : baezDuarteGramEntry 13 20 = vasyuninBEntry 13 20 := vasyuninBEntry_correct_axiom 13 20

theorem vasyuninBEntry_13_20_eval :
    ((((2653489/40110000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 20) ∧
    (vasyuninBEntry 13 20 ≤ (((2661511/40110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1320_formula_bound
  constructor <;> linarith

theorem G13_20_interval :
    ((((2653489/40110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 20) ∧
    (baezDuarteGramEntry 13 20 ≤ (((2661511/40110000) : ℚ) : ℝ)) := by
  rw [G13_20_formula]
  exact vasyuninBEntry_13_20_eval

def interval_13_20 : NamedVasyuninInterval :=
{
  h := 13
  k := 20
  lower := (2653489/40110000)
  upper := (2661511/40110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_20_interval
}

theorem G13_21_formula : baezDuarteGramEntry 13 21 = vasyuninBEntry 13 21 := vasyuninBEntry_correct_axiom 13 21

theorem vasyuninBEntry_13_21_eval :
    ((((47346051/739490000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 21) ∧
    (vasyuninBEntry 13 21 ≤ (((47493949/739490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1321_formula_bound
  constructor <;> linarith

theorem G13_21_interval :
    ((((47346051/739490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 21) ∧
    (baezDuarteGramEntry 13 21 ≤ (((47493949/739490000) : ℚ) : ℝ)) := by
  rw [G13_21_formula]
  exact vasyuninBEntry_13_21_eval

def interval_13_21 : NamedVasyuninInterval :=
{
  h := 13
  k := 21
  lower := (47346051/739490000)
  upper := (47493949/739490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_21_interval
}

theorem G13_22_formula : baezDuarteGramEntry 13 22 = vasyuninBEntry 13 22 := vasyuninBEntry_correct_axiom 13 22

theorem vasyuninBEntry_13_22_eval :
    ((((58376347/936530000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 22) ∧
    (vasyuninBEntry 13 22 ≤ (((58563653/936530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1322_formula_bound
  constructor <;> linarith

theorem G13_22_interval :
    ((((58376347/936530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 22) ∧
    (baezDuarteGramEntry 13 22 ≤ (((58563653/936530000) : ℚ) : ℝ)) := by
  rw [G13_22_formula]
  exact vasyuninBEntry_13_22_eval

def interval_13_22 : NamedVasyuninInterval :=
{
  h := 13
  k := 22
  lower := (58376347/936530000)
  upper := (58563653/936530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_22_interval
}

theorem G13_23_formula : baezDuarteGramEntry 13 23 = vasyuninBEntry 13 23 := vasyuninBEntry_correct_axiom 13 23

theorem vasyuninBEntry_13_23_eval :
    ((((23401551/384490000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 23) ∧
    (vasyuninBEntry 13 23 ≤ (((23478449/384490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1323_formula_bound
  constructor <;> linarith

theorem G13_23_interval :
    ((((23401551/384490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 23) ∧
    (baezDuarteGramEntry 13 23 ≤ (((23478449/384490000) : ℚ) : ℝ)) := by
  rw [G13_23_formula]
  exact vasyuninBEntry_13_23_eval

def interval_13_23 : NamedVasyuninInterval :=
{
  h := 13
  k := 23
  lower := (23401551/384490000)
  upper := (23478449/384490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_23_interval
}

theorem G13_24_formula : baezDuarteGramEntry 13 24 = vasyuninBEntry 13 24 := vasyuninBEntry_correct_axiom 13 24

theorem vasyuninBEntry_13_24_eval :
    ((((3969603/66470000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 24) ∧
    (vasyuninBEntry 13 24 ≤ (((3982897/66470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1324_formula_bound
  constructor <;> linarith

theorem G13_24_interval :
    ((((3969603/66470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 24) ∧
    (baezDuarteGramEntry 13 24 ≤ (((3982897/66470000) : ℚ) : ℝ)) := by
  rw [G13_24_formula]
  exact vasyuninBEntry_13_24_eval

def interval_13_24 : NamedVasyuninInterval :=
{
  h := 13
  k := 24
  lower := (3969603/66470000)
  upper := (3982897/66470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_24_interval
}

theorem G13_25_formula : baezDuarteGramEntry 13 25 = vasyuninBEntry 13 25 := vasyuninBEntry_correct_axiom 13 25

theorem vasyuninBEntry_13_25_eval :
    ((((13729231/232690000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 25) ∧
    (vasyuninBEntry 13 25 ≤ (((13775769/232690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1325_formula_bound
  constructor <;> linarith

theorem G13_25_interval :
    ((((13729231/232690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 25) ∧
    (baezDuarteGramEntry 13 25 ≤ (((13775769/232690000) : ℚ) : ℝ)) := by
  rw [G13_25_formula]
  exact vasyuninBEntry_13_25_eval

def interval_13_25 : NamedVasyuninInterval :=
{
  h := 13
  k := 25
  lower := (13729231/232690000)
  upper := (13775769/232690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_25_interval
}

theorem G13_26_formula : baezDuarteGramEntry 13 26 = vasyuninBEntry 13 26 := vasyuninBEntry_correct_axiom 13 26

theorem vasyuninBEntry_13_26_eval :
    ((((34811297/587030000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 26) ∧
    (vasyuninBEntry 13 26 ≤ (((34928703/587030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 13 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 13)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 13)
  constructor <;> linarith

theorem G13_26_interval :
    ((((34811297/587030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 26) ∧
    (baezDuarteGramEntry 13 26 ≤ (((34928703/587030000) : ℚ) : ℝ)) := by
  rw [G13_26_formula]
  exact vasyuninBEntry_13_26_eval

def interval_13_26 : NamedVasyuninInterval :=
{
  h := 13
  k := 26
  lower := (34811297/587030000)
  upper := (34928703/587030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_26_interval
}

theorem G13_27_formula : baezDuarteGramEntry 13 27 = vasyuninBEntry 13 27 := vasyuninBEntry_correct_axiom 13 27

theorem vasyuninBEntry_13_27_eval :
    ((((29647261/527390000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 27) ∧
    (vasyuninBEntry 13 27 ≤ (((29752739/527390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1327_formula_bound
  constructor <;> linarith

theorem G13_27_interval :
    ((((29647261/527390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 27) ∧
    (baezDuarteGramEntry 13 27 ≤ (((29752739/527390000) : ℚ) : ℝ)) := by
  rw [G13_27_formula]
  exact vasyuninBEntry_13_27_eval

def interval_13_27 : NamedVasyuninInterval :=
{
  h := 13
  k := 27
  lower := (29647261/527390000)
  upper := (29752739/527390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_27_interval
}

theorem G13_28_formula : baezDuarteGramEntry 13 28 = vasyuninBEntry 13 28 := vasyuninBEntry_correct_axiom 13 28

theorem vasyuninBEntry_13_28_eval :
    ((((79129/1460000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 28) ∧
    (vasyuninBEntry 13 28 ≤ (((79421/1460000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1328_formula_bound
  constructor <;> linarith

theorem G13_28_interval :
    ((((79129/1460000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 28) ∧
    (baezDuarteGramEntry 13 28 ≤ (((79421/1460000) : ℚ) : ℝ)) := by
  rw [G13_28_formula]
  exact vasyuninBEntry_13_28_eval

def interval_13_28 : NamedVasyuninInterval :=
{
  h := 13
  k := 28
  lower := (79129/1460000)
  upper := (79421/1460000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_28_interval
}

theorem G13_29_formula : baezDuarteGramEntry 13 29 = vasyuninBEntry 13 29 := vasyuninBEntry_correct_axiom 13 29

theorem vasyuninBEntry_13_29_eval :
    ((((9853757/187430000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 29) ∧
    (vasyuninBEntry 13 29 ≤ (((9891243/187430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1329_formula_bound
  constructor <;> linarith

theorem G13_29_interval :
    ((((9853757/187430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 29) ∧
    (baezDuarteGramEntry 13 29 ≤ (((9891243/187430000) : ℚ) : ℝ)) := by
  rw [G13_29_formula]
  exact vasyuninBEntry_13_29_eval

def interval_13_29 : NamedVasyuninInterval :=
{
  h := 13
  k := 29
  lower := (9853757/187430000)
  upper := (9891243/187430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_29_interval
}

theorem G13_30_formula : baezDuarteGramEntry 13 30 = vasyuninBEntry 13 30 := vasyuninBEntry_correct_axiom 13 30

theorem vasyuninBEntry_13_30_eval :
    ((((297419/5810000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 30) ∧
    (vasyuninBEntry 13 30 ≤ (((298581/5810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1330_formula_bound
  constructor <;> linarith

theorem G13_30_interval :
    ((((297419/5810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 30) ∧
    (baezDuarteGramEntry 13 30 ≤ (((298581/5810000) : ℚ) : ℝ)) := by
  rw [G13_30_formula]
  exact vasyuninBEntry_13_30_eval

def interval_13_30 : NamedVasyuninInterval :=
{
  h := 13
  k := 30
  lower := (297419/5810000)
  upper := (298581/5810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_30_interval
}

theorem G13_31_formula : baezDuarteGramEntry 13 31 = vasyuninBEntry 13 31 := vasyuninBEntry_correct_axiom 13 31

theorem vasyuninBEntry_13_31_eval :
    ((((11080317/221830000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 31) ∧
    (vasyuninBEntry 13 31 ≤ (((11124683/221830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1331_formula_bound
  constructor <;> linarith

theorem G13_31_interval :
    ((((11080317/221830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 31) ∧
    (baezDuarteGramEntry 13 31 ≤ (((11124683/221830000) : ℚ) : ℝ)) := by
  rw [G13_31_formula]
  exact vasyuninBEntry_13_31_eval

def interval_13_31 : NamedVasyuninInterval :=
{
  h := 13
  k := 31
  lower := (11080317/221830000)
  upper := (11124683/221830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_31_interval
}

theorem G13_32_formula : baezDuarteGramEntry 13 32 = vasyuninBEntry 13 32 := vasyuninBEntry_correct_axiom 13 32

theorem vasyuninBEntry_13_32_eval :
    ((((18312553/374470000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 32) ∧
    (vasyuninBEntry 13 32 ≤ (((18387447/374470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1332_formula_bound
  constructor <;> linarith

theorem G13_32_interval :
    ((((18312553/374470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 32) ∧
    (baezDuarteGramEntry 13 32 ≤ (((18387447/374470000) : ℚ) : ℝ)) := by
  rw [G13_32_formula]
  exact vasyuninBEntry_13_32_eval

def interval_13_32 : NamedVasyuninInterval :=
{
  h := 13
  k := 32
  lower := (18312553/374470000)
  upper := (18387447/374470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_32_interval
}

theorem G13_33_formula : baezDuarteGramEntry 13 33 = vasyuninBEntry 13 33 := vasyuninBEntry_correct_axiom 13 33

theorem vasyuninBEntry_13_33_eval :
    ((((6895597/144030000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 33) ∧
    (vasyuninBEntry 13 33 ≤ (((6924403/144030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1333_formula_bound
  constructor <;> linarith

theorem G13_33_interval :
    ((((6895597/144030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 33) ∧
    (baezDuarteGramEntry 13 33 ≤ (((6924403/144030000) : ℚ) : ℝ)) := by
  rw [G13_33_formula]
  exact vasyuninBEntry_13_33_eval

def interval_13_33 : NamedVasyuninInterval :=
{
  h := 13
  k := 33
  lower := (6895597/144030000)
  upper := (6924403/144030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_33_interval
}

theorem G13_34_formula : baezDuarteGramEntry 13 34 = vasyuninBEntry 13 34 := vasyuninBEntry_correct_axiom 13 34

theorem vasyuninBEntry_13_34_eval :
    ((((2316307/49430000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 34) ∧
    (vasyuninBEntry 13 34 ≤ (((2326193/49430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1334_formula_bound
  constructor <;> linarith

theorem G13_34_interval :
    ((((2316307/49430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 34) ∧
    (baezDuarteGramEntry 13 34 ≤ (((2326193/49430000) : ℚ) : ℝ)) := by
  rw [G13_34_formula]
  exact vasyuninBEntry_13_34_eval

def interval_13_34 : NamedVasyuninInterval :=
{
  h := 13
  k := 34
  lower := (2316307/49430000)
  upper := (2326193/49430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_34_interval
}

theorem G13_35_formula : baezDuarteGramEntry 13 35 = vasyuninBEntry 13 35 := vasyuninBEntry_correct_axiom 13 35

theorem vasyuninBEntry_13_35_eval :
    ((((79587/1730000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 35) ∧
    (vasyuninBEntry 13 35 ≤ (((79933/1730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1335_formula_bound
  constructor <;> linarith

theorem G13_35_interval :
    ((((79587/1730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 35) ∧
    (baezDuarteGramEntry 13 35 ≤ (((79933/1730000) : ℚ) : ℝ)) := by
  rw [G13_35_formula]
  exact vasyuninBEntry_13_35_eval

def interval_13_35 : NamedVasyuninInterval :=
{
  h := 13
  k := 35
  lower := (79587/1730000)
  upper := (79933/1730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_35_interval
}

theorem G13_36_formula : baezDuarteGramEntry 13 36 = vasyuninBEntry 13 36 := vasyuninBEntry_correct_axiom 13 36

theorem vasyuninBEntry_13_36_eval :
    ((((22570103/498970000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 36) ∧
    (vasyuninBEntry 13 36 ≤ (((22669897/498970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1336_formula_bound
  constructor <;> linarith

theorem G13_36_interval :
    ((((22570103/498970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 36) ∧
    (baezDuarteGramEntry 13 36 ≤ (((22669897/498970000) : ℚ) : ℝ)) := by
  rw [G13_36_formula]
  exact vasyuninBEntry_13_36_eval

def interval_13_36 : NamedVasyuninInterval :=
{
  h := 13
  k := 36
  lower := (22570103/498970000)
  upper := (22669897/498970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_36_interval
}

theorem G13_37_formula : baezDuarteGramEntry 13 37 = vasyuninBEntry 13 37 := vasyuninBEntry_correct_axiom 13 37

theorem vasyuninBEntry_13_37_eval :
    ((((21571627/483730000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 37) ∧
    (vasyuninBEntry 13 37 ≤ (((21668373/483730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1337_formula_bound
  constructor <;> linarith

theorem G13_37_interval :
    ((((21571627/483730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 37) ∧
    (baezDuarteGramEntry 13 37 ≤ (((21668373/483730000) : ℚ) : ℝ)) := by
  rw [G13_37_formula]
  exact vasyuninBEntry_13_37_eval

def interval_13_37 : NamedVasyuninInterval :=
{
  h := 13
  k := 37
  lower := (21571627/483730000)
  upper := (21668373/483730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_37_interval
}

theorem G13_38_formula : baezDuarteGramEntry 13 38 = vasyuninBEntry 13 38 := vasyuninBEntry_correct_axiom 13 38

theorem vasyuninBEntry_13_38_eval :
    ((((20498557/464430000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 38) ∧
    (vasyuninBEntry 13 38 ≤ (((20591443/464430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1338_formula_bound
  constructor <;> linarith

theorem G13_38_interval :
    ((((20498557/464430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 38) ∧
    (baezDuarteGramEntry 13 38 ≤ (((20591443/464430000) : ℚ) : ℝ)) := by
  rw [G13_38_formula]
  exact vasyuninBEntry_13_38_eval

def interval_13_38 : NamedVasyuninInterval :=
{
  h := 13
  k := 38
  lower := (20498557/464430000)
  upper := (20591443/464430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_38_interval
}

theorem G13_39_formula : baezDuarteGramEntry 13 39 = vasyuninBEntry 13 39 := vasyuninBEntry_correct_axiom 13 39

theorem vasyuninBEntry_13_39_eval :
    ((((34970757/792430000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 39) ∧
    (vasyuninBEntry 13 39 ≤ (((35129243/792430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 13 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 13)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 13)
  constructor <;> linarith

theorem G13_39_interval :
    ((((34970757/792430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 39) ∧
    (baezDuarteGramEntry 13 39 ≤ (((35129243/792430000) : ℚ) : ℝ)) := by
  rw [G13_39_formula]
  exact vasyuninBEntry_13_39_eval

def interval_13_39 : NamedVasyuninInterval :=
{
  h := 13
  k := 39
  lower := (34970757/792430000)
  upper := (35129243/792430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_39_interval
}

theorem G13_40_formula : baezDuarteGramEntry 13 40 = vasyuninBEntry 13 40 := vasyuninBEntry_correct_axiom 13 40

theorem vasyuninBEntry_13_40_eval :
    ((((6708259/157410000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 40) ∧
    (vasyuninBEntry 13 40 ≤ (((6739741/157410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1340_formula_bound
  constructor <;> linarith

theorem G13_40_interval :
    ((((6708259/157410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 40) ∧
    (baezDuarteGramEntry 13 40 ≤ (((6739741/157410000) : ℚ) : ℝ)) := by
  rw [G13_40_formula]
  exact vasyuninBEntry_13_40_eval

def interval_13_40 : NamedVasyuninInterval :=
{
  h := 13
  k := 40
  lower := (6708259/157410000)
  upper := (6739741/157410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_40_interval
}

theorem G13_41_formula : baezDuarteGramEntry 13 41 = vasyuninBEntry 13 41 := vasyuninBEntry_correct_axiom 13 41

theorem vasyuninBEntry_13_41_eval :
    ((((1534309/36910000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 41) ∧
    (vasyuninBEntry 13 41 ≤ (((1541691/36910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1341_formula_bound
  constructor <;> linarith

theorem G13_41_interval :
    ((((1534309/36910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 41) ∧
    (baezDuarteGramEntry 13 41 ≤ (((1541691/36910000) : ℚ) : ℝ)) := by
  rw [G13_41_formula]
  exact vasyuninBEntry_13_41_eval

def interval_13_41 : NamedVasyuninInterval :=
{
  h := 13
  k := 41
  lower := (1534309/36910000)
  upper := (1541691/36910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_41_interval
}

theorem G13_42_formula : baezDuarteGramEntry 13 42 = vasyuninBEntry 13 42 := vasyuninBEntry_correct_axiom 13 42

theorem vasyuninBEntry_13_42_eval :
    ((((4696459/115410000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 42) ∧
    (vasyuninBEntry 13 42 ≤ (((4719541/115410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1342_formula_bound
  constructor <;> linarith

theorem G13_42_interval :
    ((((4696459/115410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 42) ∧
    (baezDuarteGramEntry 13 42 ≤ (((4719541/115410000) : ℚ) : ℝ)) := by
  rw [G13_42_formula]
  exact vasyuninBEntry_13_42_eval

def interval_13_42 : NamedVasyuninInterval :=
{
  h := 13
  k := 42
  lower := (4696459/115410000)
  upper := (4719541/115410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_42_interval
}

theorem G13_43_formula : baezDuarteGramEntry 13 43 = vasyuninBEntry 13 43 := vasyuninBEntry_correct_axiom 13 43

theorem vasyuninBEntry_13_43_eval :
    ((((3418937/85630000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 43) ∧
    (vasyuninBEntry 13 43 ≤ (((3436063/85630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1343_formula_bound
  constructor <;> linarith

theorem G13_43_interval :
    ((((3418937/85630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 43) ∧
    (baezDuarteGramEntry 13 43 ≤ (((3436063/85630000) : ℚ) : ℝ)) := by
  rw [G13_43_formula]
  exact vasyuninBEntry_13_43_eval

def interval_13_43 : NamedVasyuninInterval :=
{
  h := 13
  k := 43
  lower := (3418937/85630000)
  upper := (3436063/85630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_43_interval
}

theorem G13_44_formula : baezDuarteGramEntry 13 44 = vasyuninBEntry 13 44 := vasyuninBEntry_correct_axiom 13 44

theorem vasyuninBEntry_13_44_eval :
    ((((33265189/848110000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 44) ∧
    (vasyuninBEntry 13 44 ≤ (((33434811/848110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1344_formula_bound
  constructor <;> linarith

theorem G13_44_interval :
    ((((33265189/848110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 44) ∧
    (baezDuarteGramEntry 13 44 ≤ (((33434811/848110000) : ℚ) : ℝ)) := by
  rw [G13_44_formula]
  exact vasyuninBEntry_13_44_eval

def interval_13_44 : NamedVasyuninInterval :=
{
  h := 13
  k := 44
  lower := (33265189/848110000)
  upper := (33434811/848110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_44_interval
}

theorem G13_45_formula : baezDuarteGramEntry 13 45 = vasyuninBEntry 13 45 := vasyuninBEntry_correct_axiom 13 45

theorem vasyuninBEntry_13_45_eval :
    ((((4076941/105590000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 45) ∧
    (vasyuninBEntry 13 45 ≤ (((4098059/105590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1345_formula_bound
  constructor <;> linarith

theorem G13_45_interval :
    ((((4076941/105590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 45) ∧
    (baezDuarteGramEntry 13 45 ≤ (((4098059/105590000) : ℚ) : ℝ)) := by
  rw [G13_45_formula]
  exact vasyuninBEntry_13_45_eval

def interval_13_45 : NamedVasyuninInterval :=
{
  h := 13
  k := 45
  lower := (4076941/105590000)
  upper := (4098059/105590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_45_interval
}

theorem G13_46_formula : baezDuarteGramEntry 13 46 = vasyuninBEntry 13 46 := vasyuninBEntry_correct_axiom 13 46

theorem vasyuninBEntry_13_46_eval :
    ((((8293179/218210000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 46) ∧
    (vasyuninBEntry 13 46 ≤ (((8336821/218210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1346_formula_bound
  constructor <;> linarith

theorem G13_46_interval :
    ((((8293179/218210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 46) ∧
    (baezDuarteGramEntry 13 46 ≤ (((8336821/218210000) : ℚ) : ℝ)) := by
  rw [G13_46_formula]
  exact vasyuninBEntry_13_46_eval

def interval_13_46 : NamedVasyuninInterval :=
{
  h := 13
  k := 46
  lower := (8293179/218210000)
  upper := (8336821/218210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_46_interval
}

theorem G13_47_formula : baezDuarteGramEntry 13 47 = vasyuninBEntry 13 47 := vasyuninBEntry_correct_axiom 13 47

theorem vasyuninBEntry_13_47_eval :
    ((((16052083/429170000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 47) ∧
    (vasyuninBEntry 13 47 ≤ (((16137917/429170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1347_formula_bound
  constructor <;> linarith

theorem G13_47_interval :
    ((((16052083/429170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 47) ∧
    (baezDuarteGramEntry 13 47 ≤ (((16137917/429170000) : ℚ) : ℝ)) := by
  rw [G13_47_formula]
  exact vasyuninBEntry_13_47_eval

def interval_13_47 : NamedVasyuninInterval :=
{
  h := 13
  k := 47
  lower := (16052083/429170000)
  upper := (16137917/429170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_47_interval
}

theorem G13_48_formula : baezDuarteGramEntry 13 48 = vasyuninBEntry 13 48 := vasyuninBEntry_correct_axiom 13 48

theorem vasyuninBEntry_13_48_eval :
    ((((239351/6490000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 48) ∧
    (vasyuninBEntry 13 48 ≤ (((240649/6490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1348_formula_bound
  constructor <;> linarith

theorem G13_48_interval :
    ((((239351/6490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 48) ∧
    (baezDuarteGramEntry 13 48 ≤ (((240649/6490000) : ℚ) : ℝ)) := by
  rw [G13_48_formula]
  exact vasyuninBEntry_13_48_eval

def interval_13_48 : NamedVasyuninInterval :=
{
  h := 13
  k := 48
  lower := (239351/6490000)
  upper := (240649/6490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_48_interval
}

theorem G13_49_formula : baezDuarteGramEntry 13 49 = vasyuninBEntry 13 49 := vasyuninBEntry_correct_axiom 13 49

theorem vasyuninBEntry_13_49_eval :
    ((((23784659/653410000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 49) ∧
    (vasyuninBEntry 13 49 ≤ (((23915341/653410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1349_formula_bound
  constructor <;> linarith

theorem G13_49_interval :
    ((((23784659/653410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 49) ∧
    (baezDuarteGramEntry 13 49 ≤ (((23915341/653410000) : ℚ) : ℝ)) := by
  rw [G13_49_formula]
  exact vasyuninBEntry_13_49_eval

def interval_13_49 : NamedVasyuninInterval :=
{
  h := 13
  k := 49
  lower := (23784659/653410000)
  upper := (23915341/653410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_49_interval
}

theorem G13_50_formula : baezDuarteGramEntry 13 50 = vasyuninBEntry 13 50 := vasyuninBEntry_correct_axiom 13 50

theorem vasyuninBEntry_13_50_eval :
    ((((1159279/32210000) : ℚ) : ℝ) ≤ vasyuninBEntry 13 50) ∧
    (vasyuninBEntry 13 50 ≤ (((1165721/32210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1350_formula_bound
  constructor <;> linarith

theorem G13_50_interval :
    ((((1159279/32210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 13 50) ∧
    (baezDuarteGramEntry 13 50 ≤ (((1165721/32210000) : ℚ) : ℝ)) := by
  rw [G13_50_formula]
  exact vasyuninBEntry_13_50_eval

def interval_13_50 : NamedVasyuninInterval :=
{
  h := 13
  k := 50
  lower := (1159279/32210000)
  upper := (1165721/32210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G13_50_interval
}

theorem G14_1_formula : baezDuarteGramEntry 14 1 = vasyuninBEntry 1 14 := by
  rw [baezDuarteGramEntry_symm 14 1]
  exact G1_14_formula

theorem G14_1_interval :
    ((((150274417/855830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 1) ∧
    (baezDuarteGramEntry 14 1 ≤ (((150445583/855830000) : ℚ) : ℝ)) := by
  rw [G14_1_formula]
  exact vasyuninBEntry_1_14_eval

def interval_14_1 : NamedVasyuninInterval :=
{
  h := 14
  k := 1
  lower := (150274417/855830000)
  upper := (150445583/855830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_1_interval
}

theorem G14_2_formula : baezDuarteGramEntry 14 2 = vasyuninBEntry 2 14 := by
  rw [baezDuarteGramEntry_symm 14 2]
  exact G2_14_formula

theorem G14_2_interval :
    ((((77688731/512690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 2) ∧
    (baezDuarteGramEntry 14 2 ≤ (((77791269/512690000) : ℚ) : ℝ)) := by
  rw [G14_2_formula]
  exact vasyuninBEntry_2_14_eval

def interval_14_2 : NamedVasyuninInterval :=
{
  h := 14
  k := 2
  lower := (77688731/512690000)
  upper := (77791269/512690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_2_interval
}

theorem G14_3_formula : baezDuarteGramEntry 14 3 = vasyuninBEntry 3 14 := by
  rw [baezDuarteGramEntry_symm 14 3]
  exact G3_14_formula

theorem G14_3_interval :
    ((((110508283/817170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 3) ∧
    (baezDuarteGramEntry 14 3 ≤ (((110671717/817170000) : ℚ) : ℝ)) := by
  rw [G14_3_formula]
  exact vasyuninBEntry_3_14_eval

def interval_14_3 : NamedVasyuninInterval :=
{
  h := 14
  k := 3
  lower := (110508283/817170000)
  upper := (110671717/817170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_3_interval
}

theorem G14_4_formula : baezDuarteGramEntry 14 4 = vasyuninBEntry 4 14 := by
  rw [baezDuarteGramEntry_symm 14 4]
  exact G4_14_formula

theorem G14_4_interval :
    ((((103337357/826430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 4) ∧
    (baezDuarteGramEntry 14 4 ≤ (((103502643/826430000) : ℚ) : ℝ)) := by
  rw [G14_4_formula]
  exact vasyuninBEntry_4_14_eval

def interval_14_4 : NamedVasyuninInterval :=
{
  h := 14
  k := 4
  lower := (103337357/826430000)
  upper := (103502643/826430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_4_interval
}

theorem G14_5_formula : baezDuarteGramEntry 14 5 = vasyuninBEntry 5 14 := by
  rw [baezDuarteGramEntry_symm 14 5]
  exact G5_14_formula

theorem G14_5_interval :
    ((((3848713/32870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 5) ∧
    (baezDuarteGramEntry 14 5 ≤ (((3855287/32870000) : ℚ) : ℝ)) := by
  rw [G14_5_formula]
  exact vasyuninBEntry_5_14_eval

def interval_14_5 : NamedVasyuninInterval :=
{
  h := 14
  k := 5
  lower := (3848713/32870000)
  upper := (3855287/32870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_5_interval
}

theorem G14_6_formula : baezDuarteGramEntry 14 6 = vasyuninBEntry 6 14 := by
  rw [baezDuarteGramEntry_symm 14 6]
  exact G6_14_formula

theorem G14_6_interval :
    ((((2713939/24610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 6) ∧
    (baezDuarteGramEntry 14 6 ≤ (((2718861/24610000) : ℚ) : ℝ)) := by
  rw [G14_6_formula]
  exact vasyuninBEntry_6_14_eval

def interval_14_6 : NamedVasyuninInterval :=
{
  h := 14
  k := 6
  lower := (2713939/24610000)
  upper := (2718861/24610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_6_interval
}

theorem G14_7_formula : baezDuarteGramEntry 14 7 = vasyuninBEntry 7 14 := by
  rw [baezDuarteGramEntry_symm 14 7]
  exact G7_14_formula

theorem G14_7_interval :
    ((((52417441/475590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 7) ∧
    (baezDuarteGramEntry 14 7 ≤ (((52512559/475590000) : ℚ) : ℝ)) := by
  rw [G14_7_formula]
  exact vasyuninBEntry_7_14_eval

def interval_14_7 : NamedVasyuninInterval :=
{
  h := 14
  k := 7
  lower := (52417441/475590000)
  upper := (52512559/475590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_7_interval
}

theorem G14_8_formula : baezDuarteGramEntry 14 8 = vasyuninBEntry 8 14 := by
  rw [baezDuarteGramEntry_symm 14 8]
  exact G8_14_formula

theorem G14_8_interval :
    ((((24685219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 8) ∧
    (baezDuarteGramEntry 14 8 ≤ (((24734781/247810000) : ℚ) : ℝ)) := by
  rw [G14_8_formula]
  exact vasyuninBEntry_8_14_eval

def interval_14_8 : NamedVasyuninInterval :=
{
  h := 14
  k := 8
  lower := (24685219/247810000)
  upper := (24734781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_8_interval
}

theorem G14_9_formula : baezDuarteGramEntry 14 9 = vasyuninBEntry 9 14 := by
  rw [baezDuarteGramEntry_symm 14 9]
  exact G9_14_formula

theorem G14_9_interval :
    ((((23572643/248570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 9) ∧
    (baezDuarteGramEntry 14 9 ≤ (((23622357/248570000) : ℚ) : ℝ)) := by
  rw [G14_9_formula]
  exact vasyuninBEntry_9_14_eval

def interval_14_9 : NamedVasyuninInterval :=
{
  h := 14
  k := 9
  lower := (23572643/248570000)
  upper := (23622357/248570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_9_interval
}

theorem G14_10_formula : baezDuarteGramEntry 14 10 = vasyuninBEntry 10 14 := by
  rw [baezDuarteGramEntry_symm 14 10]
  exact G10_14_formula

theorem G14_10_interval :
    ((((18160087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 10) ∧
    (baezDuarteGramEntry 14 10 ≤ (((18199913/199130000) : ℚ) : ℝ)) := by
  rw [G14_10_formula]
  exact vasyuninBEntry_10_14_eval

def interval_14_10 : NamedVasyuninInterval :=
{
  h := 14
  k := 10
  lower := (18160087/199130000)
  upper := (18199913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_10_interval
}

theorem G14_11_formula : baezDuarteGramEntry 14 11 = vasyuninBEntry 11 14 := by
  rw [baezDuarteGramEntry_symm 14 11]
  exact G11_14_formula

theorem G14_11_interval :
    ((((52111121/588790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 11) ∧
    (baezDuarteGramEntry 14 11 ≤ (((52228879/588790000) : ℚ) : ℝ)) := by
  rw [G14_11_formula]
  exact vasyuninBEntry_11_14_eval

def interval_14_11 : NamedVasyuninInterval :=
{
  h := 14
  k := 11
  lower := (52111121/588790000)
  upper := (52228879/588790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_11_interval
}

theorem G14_12_formula : baezDuarteGramEntry 14 12 = vasyuninBEntry 12 14 := by
  rw [baezDuarteGramEntry_symm 14 12]
  exact G12_14_formula

theorem G14_12_interval :
    ((((40833059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 12) ∧
    (baezDuarteGramEntry 14 12 ≤ (((40926941/469410000) : ℚ) : ℝ)) := by
  rw [G14_12_formula]
  exact vasyuninBEntry_12_14_eval

def interval_14_12 : NamedVasyuninInterval :=
{
  h := 14
  k := 12
  lower := (40833059/469410000)
  upper := (40926941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_12_interval
}

theorem G14_13_formula : baezDuarteGramEntry 14 13 = vasyuninBEntry 13 14 := by
  rw [baezDuarteGramEntry_symm 14 13]
  exact G13_14_formula

theorem G14_13_interval :
    ((((80816869/931310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 13) ∧
    (baezDuarteGramEntry 14 13 ≤ (((81003131/931310000) : ℚ) : ℝ)) := by
  rw [G14_13_formula]
  exact vasyuninBEntry_13_14_eval

def interval_14_13 : NamedVasyuninInterval :=
{
  h := 14
  k := 13
  lower := (80816869/931310000)
  upper := (81003131/931310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_13_interval
}

theorem G14_14_formula_eq : baezDuarteGramEntry 14 14 = (1 / (14 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 14 := by norm_num
  rw [baez_duarte_diagonal_scaling 14 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G14_14_log_gamma_interval :
  ((((28368461/315390000) : ℚ) : ℝ) ≤ (1 / (14 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (14 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((28431539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 14 (by norm_num)
  constructor
  · have : ((((28368461/315390000) : ℚ) : ℝ) ≤ (1 / (14 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (14 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((28431539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G14_14_interval : ((((28368461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 14) ∧ (baezDuarteGramEntry 14 14 ≤ (((28431539/315390000) : ℚ) : ℝ)) := by
  rw [G14_14_formula_eq]
  exact G14_14_log_gamma_interval

def interval_14_14 : NamedVasyuninInterval :=
{
  h := 14
  k := 14
  lower := (28368461/315390000)
  upper := (28431539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G14_14_interval
}

theorem G14_15_formula : baezDuarteGramEntry 14 15 = vasyuninBEntry 14 15 := vasyuninBEntry_correct_axiom 14 15

theorem vasyuninBEntry_14_15_eval :
    ((((49139363/606370000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 15) ∧
    (vasyuninBEntry 14 15 ≤ (((49260637/606370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1415_formula_bound
  constructor <;> linarith

theorem G14_15_interval :
    ((((49139363/606370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 15) ∧
    (baezDuarteGramEntry 14 15 ≤ (((49260637/606370000) : ℚ) : ℝ)) := by
  rw [G14_15_formula]
  exact vasyuninBEntry_14_15_eval

def interval_14_15 : NamedVasyuninInterval :=
{
  h := 14
  k := 15
  lower := (49139363/606370000)
  upper := (49260637/606370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_15_interval
}

theorem G14_16_formula : baezDuarteGramEntry 14 16 = vasyuninBEntry 14 16 := vasyuninBEntry_correct_axiom 14 16

theorem vasyuninBEntry_14_16_eval :
    ((((55417003/729970000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 16) ∧
    (vasyuninBEntry 14 16 ≤ (((55562997/729970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 8 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_16_interval :
    ((((55417003/729970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 16) ∧
    (baezDuarteGramEntry 14 16 ≤ (((55562997/729970000) : ℚ) : ℝ)) := by
  rw [G14_16_formula]
  exact vasyuninBEntry_14_16_eval

def interval_14_16 : NamedVasyuninInterval :=
{
  h := 14
  k := 16
  lower := (55417003/729970000)
  upper := (55562997/729970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_16_interval
}

theorem G14_17_formula : baezDuarteGramEntry 14 17 = vasyuninBEntry 14 17 := vasyuninBEntry_correct_axiom 14 17

theorem vasyuninBEntry_14_17_eval :
    ((((552753/7670000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 17) ∧
    (vasyuninBEntry 14 17 ≤ (((554287/7670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1417_formula_bound
  constructor <;> linarith

theorem G14_17_interval :
    ((((552753/7670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 17) ∧
    (baezDuarteGramEntry 14 17 ≤ (((554287/7670000) : ℚ) : ℝ)) := by
  rw [G14_17_formula]
  exact vasyuninBEntry_14_17_eval

def interval_14_17 : NamedVasyuninInterval :=
{
  h := 14
  k := 17
  lower := (552753/7670000)
  upper := (554287/7670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_17_interval
}

theorem G14_18_formula : baezDuarteGramEntry 14 18 = vasyuninBEntry 14 18 := vasyuninBEntry_correct_axiom 14 18

theorem vasyuninBEntry_14_18_eval :
    ((((11691061/169390000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 18) ∧
    (vasyuninBEntry 14 18 ≤ (((11724939/169390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 9 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_18_interval :
    ((((11691061/169390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 18) ∧
    (baezDuarteGramEntry 14 18 ≤ (((11724939/169390000) : ℚ) : ℝ)) := by
  rw [G14_18_formula]
  exact vasyuninBEntry_14_18_eval

def interval_14_18 : NamedVasyuninInterval :=
{
  h := 14
  k := 18
  lower := (11691061/169390000)
  upper := (11724939/169390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_18_interval
}

theorem G14_19_formula : baezDuarteGramEntry 14 19 = vasyuninBEntry 14 19 := vasyuninBEntry_correct_axiom 14 19

theorem vasyuninBEntry_14_19_eval :
    ((((19860119/298810000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 19) ∧
    (vasyuninBEntry 14 19 ≤ (((19919881/298810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1419_formula_bound
  constructor <;> linarith

theorem G14_19_interval :
    ((((19860119/298810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 19) ∧
    (baezDuarteGramEntry 14 19 ≤ (((19919881/298810000) : ℚ) : ℝ)) := by
  rw [G14_19_formula]
  exact vasyuninBEntry_14_19_eval

def interval_14_19 : NamedVasyuninInterval :=
{
  h := 14
  k := 19
  lower := (19860119/298810000)
  upper := (19919881/298810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_19_interval
}

theorem G14_20_formula : baezDuarteGramEntry 14 20 = vasyuninBEntry 14 20 := vasyuninBEntry_correct_axiom 14 20

theorem vasyuninBEntry_14_20_eval :
    ((((43302617/673830000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 20) ∧
    (vasyuninBEntry 14 20 ≤ (((43437383/673830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 10 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_20_interval :
    ((((43302617/673830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 20) ∧
    (baezDuarteGramEntry 14 20 ≤ (((43437383/673830000) : ℚ) : ℝ)) := by
  rw [G14_20_formula]
  exact vasyuninBEntry_14_20_eval

def interval_14_20 : NamedVasyuninInterval :=
{
  h := 14
  k := 20
  lower := (43302617/673830000)
  upper := (43437383/673830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_20_interval
}

theorem G14_21_formula : baezDuarteGramEntry 14 21 = vasyuninBEntry 14 21 := vasyuninBEntry_correct_axiom 14 21

theorem vasyuninBEntry_14_21_eval :
    ((((58586879/931210000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 21) ∧
    (vasyuninBEntry 14 21 ≤ (((58773121/931210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G14_21_interval :
    ((((58586879/931210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 21) ∧
    (baezDuarteGramEntry 14 21 ≤ (((58773121/931210000) : ℚ) : ℝ)) := by
  rw [G14_21_formula]
  exact vasyuninBEntry_14_21_eval

def interval_14_21 : NamedVasyuninInterval :=
{
  h := 14
  k := 21
  lower := (58586879/931210000)
  upper := (58773121/931210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_21_interval
}

theorem G14_22_formula : baezDuarteGramEntry 14 22 = vasyuninBEntry 14 22 := vasyuninBEntry_correct_axiom 14 22

theorem vasyuninBEntry_14_22_eval :
    ((((58543251/967490000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 22) ∧
    (vasyuninBEntry 14 22 ≤ (((58736749/967490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 11 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_22_interval :
    ((((58543251/967490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 22) ∧
    (baezDuarteGramEntry 14 22 ≤ (((58736749/967490000) : ℚ) : ℝ)) := by
  rw [G14_22_formula]
  exact vasyuninBEntry_14_22_eval

def interval_14_22 : NamedVasyuninInterval :=
{
  h := 14
  k := 22
  lower := (58543251/967490000)
  upper := (58736749/967490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_22_interval
}

theorem G14_23_formula : baezDuarteGramEntry 14 23 = vasyuninBEntry 14 23 := vasyuninBEntry_correct_axiom 14 23

theorem vasyuninBEntry_14_23_eval :
    ((((38664323/656770000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 23) ∧
    (vasyuninBEntry 14 23 ≤ (((38795677/656770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1423_formula_bound
  constructor <;> linarith

theorem G14_23_interval :
    ((((38664323/656770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 23) ∧
    (baezDuarteGramEntry 14 23 ≤ (((38795677/656770000) : ℚ) : ℝ)) := by
  rw [G14_23_formula]
  exact vasyuninBEntry_14_23_eval

def interval_14_23 : NamedVasyuninInterval :=
{
  h := 14
  k := 23
  lower := (38664323/656770000)
  upper := (38795677/656770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_23_interval
}

theorem G14_24_formula : baezDuarteGramEntry 14 24 = vasyuninBEntry 14 24 := vasyuninBEntry_correct_axiom 14 24

theorem vasyuninBEntry_14_24_eval :
    ((((47357571/824290000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 24) ∧
    (vasyuninBEntry 14 24 ≤ (((47522429/824290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 12 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_24_interval :
    ((((47357571/824290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 24) ∧
    (baezDuarteGramEntry 14 24 ≤ (((47522429/824290000) : ℚ) : ℝ)) := by
  rw [G14_24_formula]
  exact vasyuninBEntry_14_24_eval

def interval_14_24 : NamedVasyuninInterval :=
{
  h := 14
  k := 24
  lower := (47357571/824290000)
  upper := (47522429/824290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_24_interval
}

theorem G14_25_formula : baezDuarteGramEntry 14 25 = vasyuninBEntry 14 25 := vasyuninBEntry_correct_axiom 14 25

theorem vasyuninBEntry_14_25_eval :
    ((((8859251/157490000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 25) ∧
    (vasyuninBEntry 14 25 ≤ (((8890749/157490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1425_formula_bound
  constructor <;> linarith

theorem G14_25_interval :
    ((((8859251/157490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 25) ∧
    (baezDuarteGramEntry 14 25 ≤ (((8890749/157490000) : ℚ) : ℝ)) := by
  rw [G14_25_formula]
  exact vasyuninBEntry_14_25_eval

def interval_14_25 : NamedVasyuninInterval :=
{
  h := 14
  k := 25
  lower := (8859251/157490000)
  upper := (8890749/157490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_25_interval
}

theorem G14_26_formula : baezDuarteGramEntry 14 26 = vasyuninBEntry 14 26 := vasyuninBEntry_correct_axiom 14 26

theorem vasyuninBEntry_14_26_eval :
    ((((1105003/19970000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 26) ∧
    (vasyuninBEntry 14 26 ≤ (((1108997/19970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 13 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_26_interval :
    ((((1105003/19970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 26) ∧
    (baezDuarteGramEntry 14 26 ≤ (((1108997/19970000) : ℚ) : ℝ)) := by
  rw [G14_26_formula]
  exact vasyuninBEntry_14_26_eval

def interval_14_26 : NamedVasyuninInterval :=
{
  h := 14
  k := 26
  lower := (1105003/19970000)
  upper := (1108997/19970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_26_interval
}

theorem G14_27_formula : baezDuarteGramEntry 14 27 = vasyuninBEntry 14 27 := vasyuninBEntry_correct_axiom 14 27

theorem vasyuninBEntry_14_27_eval :
    ((((13547757/247430000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 27) ∧
    (vasyuninBEntry 14 27 ≤ (((13597243/247430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1427_formula_bound
  constructor <;> linarith

theorem G14_27_interval :
    ((((13547757/247430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 27) ∧
    (baezDuarteGramEntry 14 27 ≤ (((13597243/247430000) : ℚ) : ℝ)) := by
  rw [G14_27_formula]
  exact vasyuninBEntry_14_27_eval

def interval_14_27 : NamedVasyuninInterval :=
{
  h := 14
  k := 27
  lower := (13547757/247430000)
  upper := (13597243/247430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_27_interval
}

theorem G14_28_formula : baezDuarteGramEntry 14 28 = vasyuninBEntry 14 28 := vasyuninBEntry_correct_axiom 14 28

theorem vasyuninBEntry_14_28_eval :
    ((((24300863/441370000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 28) ∧
    (vasyuninBEntry 14 28 ≤ (((24389137/441370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 14 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 14)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 14)
  constructor <;> linarith

theorem G14_28_interval :
    ((((24300863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 28) ∧
    (baezDuarteGramEntry 14 28 ≤ (((24389137/441370000) : ℚ) : ℝ)) := by
  rw [G14_28_formula]
  exact vasyuninBEntry_14_28_eval

def interval_14_28 : NamedVasyuninInterval :=
{
  h := 14
  k := 28
  lower := (24300863/441370000)
  upper := (24389137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_28_interval
}

theorem G14_29_formula : baezDuarteGramEntry 14 29 = vasyuninBEntry 14 29 := vasyuninBEntry_correct_axiom 14 29

theorem vasyuninBEntry_14_29_eval :
    ((((43447003/829970000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 29) ∧
    (vasyuninBEntry 14 29 ≤ (((43612997/829970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1429_formula_bound
  constructor <;> linarith

theorem G14_29_interval :
    ((((43447003/829970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 29) ∧
    (baezDuarteGramEntry 14 29 ≤ (((43612997/829970000) : ℚ) : ℝ)) := by
  rw [G14_29_formula]
  exact vasyuninBEntry_14_29_eval

def interval_14_29 : NamedVasyuninInterval :=
{
  h := 14
  k := 29
  lower := (43447003/829970000)
  upper := (43612997/829970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_29_interval
}

theorem G14_30_formula : baezDuarteGramEntry 14 30 = vasyuninBEntry 14 30 := vasyuninBEntry_correct_axiom 14 30

theorem vasyuninBEntry_14_30_eval :
    ((((14451421/285790000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 30) ∧
    (vasyuninBEntry 14 30 ≤ (((14508579/285790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 15 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_30_interval :
    ((((14451421/285790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 30) ∧
    (baezDuarteGramEntry 14 30 ≤ (((14508579/285790000) : ℚ) : ℝ)) := by
  rw [G14_30_formula]
  exact vasyuninBEntry_14_30_eval

def interval_14_30 : NamedVasyuninInterval :=
{
  h := 14
  k := 30
  lower := (14451421/285790000)
  upper := (14508579/285790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_30_interval
}

theorem G14_31_formula : baezDuarteGramEntry 14 31 = vasyuninBEntry 14 31 := vasyuninBEntry_correct_axiom 14 31

theorem vasyuninBEntry_14_31_eval :
    ((((48012237/977630000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 31) ∧
    (vasyuninBEntry 14 31 ≤ (((48207763/977630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1431_formula_bound
  constructor <;> linarith

theorem G14_31_interval :
    ((((48012237/977630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 31) ∧
    (baezDuarteGramEntry 14 31 ≤ (((48207763/977630000) : ℚ) : ℝ)) := by
  rw [G14_31_formula]
  exact vasyuninBEntry_14_31_eval

def interval_14_31 : NamedVasyuninInterval :=
{
  h := 14
  k := 31
  lower := (48012237/977630000)
  upper := (48207763/977630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_31_interval
}

theorem G14_32_formula : baezDuarteGramEntry 14 32 = vasyuninBEntry 14 32 := vasyuninBEntry_correct_axiom 14 32

theorem vasyuninBEntry_14_32_eval :
    ((((522309/10910000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 32) ∧
    (vasyuninBEntry 14 32 ≤ (((524491/10910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 16 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_32_interval :
    ((((522309/10910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 32) ∧
    (baezDuarteGramEntry 14 32 ≤ (((524491/10910000) : ℚ) : ℝ)) := by
  rw [G14_32_formula]
  exact vasyuninBEntry_14_32_eval

def interval_14_32 : NamedVasyuninInterval :=
{
  h := 14
  k := 32
  lower := (522309/10910000)
  upper := (524491/10910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_32_interval
}

theorem G14_33_formula : baezDuarteGramEntry 14 33 = vasyuninBEntry 14 33 := vasyuninBEntry_correct_axiom 14 33

theorem vasyuninBEntry_14_33_eval :
    ((((4819697/103030000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 33) ∧
    (vasyuninBEntry 14 33 ≤ (((4840303/103030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1433_formula_bound
  constructor <;> linarith

theorem G14_33_interval :
    ((((4819697/103030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 33) ∧
    (baezDuarteGramEntry 14 33 ≤ (((4840303/103030000) : ℚ) : ℝ)) := by
  rw [G14_33_formula]
  exact vasyuninBEntry_14_33_eval

def interval_14_33 : NamedVasyuninInterval :=
{
  h := 14
  k := 33
  lower := (4819697/103030000)
  upper := (4840303/103030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_33_interval
}

theorem G14_34_formula : baezDuarteGramEntry 14 34 = vasyuninBEntry 14 34 := vasyuninBEntry_correct_axiom 14 34

theorem vasyuninBEntry_14_34_eval :
    ((((5927057/129430000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 34) ∧
    (vasyuninBEntry 14 34 ≤ (((5952943/129430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 17 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G14_34_interval :
    ((((5927057/129430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 14 34) ∧
    (baezDuarteGramEntry 14 34 ≤ (((5952943/129430000) : ℚ) : ℝ)) := by
  rw [G14_34_formula]
  exact vasyuninBEntry_14_34_eval

def interval_14_34 : NamedVasyuninInterval :=
{
  h := 14
  k := 34
  lower := (5927057/129430000)
  upper := (5952943/129430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G14_34_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
