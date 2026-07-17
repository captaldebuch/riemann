import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G1_1_formula_eq : baezDuarteGramEntry 1 1 = (1 / (1 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 1 := by norm_num
  rw [baez_duarte_diagonal_scaling 1 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G1_1_log_gamma_interval :
  ((((6303/5000) : ℚ) : ℝ) ≤ (1 / (1 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (1 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((12607/10000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 1 (by norm_num)
  constructor
  · have : ((((6303/5000) : ℚ) : ℝ) ≤ (1 / (1 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (1 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((12607/10000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G1_1_interval : ((((6303/5000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 1) ∧ (baezDuarteGramEntry 1 1 ≤ (((12607/10000) : ℚ) : ℝ)) := by
  rw [G1_1_formula_eq]
  exact G1_1_log_gamma_interval

def interval_1_1 : NamedVasyuninInterval :=
{
  h := 1
  k := 1
  lower := (6303/5000)
  upper := (12607/10000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G1_1_interval
}

theorem G1_2_formula : baezDuarteGramEntry 1 2 = vasyuninBEntry 1 2 := vasyuninBEntry_correct_axiom 1 2

theorem vasyuninBEntry_1_2_eval :
    ((((3861/5000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 2) ∧
    (vasyuninBEntry 1 2 ≤ (((7723/10000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_12_formula_bound
  constructor <;> linarith

theorem G1_2_interval :
    ((((3861/5000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 2) ∧
    (baezDuarteGramEntry 1 2 ≤ (((7723/10000) : ℚ) : ℝ)) := by
  rw [G1_2_formula]
  exact vasyuninBEntry_1_2_eval

def interval_1_2 : NamedVasyuninInterval :=
{
  h := 1
  k := 2
  lower := (3861/5000)
  upper := (7723/10000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_2_interval
}

theorem G1_3_formula : baezDuarteGramEntry 1 3 = vasyuninBEntry 1 3 := vasyuninBEntry_correct_axiom 1 3

theorem vasyuninBEntry_1_3_eval :
    ((((23/40) : ℚ) : ℝ) ≤ vasyuninBEntry 1 3) ∧
    (vasyuninBEntry 1 3 ≤ (((5751/10000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_13_formula_bound
  constructor <;> linarith

theorem G1_3_interval :
    ((((23/40) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 3) ∧
    (baezDuarteGramEntry 1 3 ≤ (((5751/10000) : ℚ) : ℝ)) := by
  rw [G1_3_formula]
  exact vasyuninBEntry_1_3_eval

def interval_1_3 : NamedVasyuninInterval :=
{
  h := 1
  k := 3
  lower := (23/40)
  upper := (5751/10000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_3_interval
}

theorem G1_4_formula : baezDuarteGramEntry 1 4 = vasyuninBEntry 1 4 := vasyuninBEntry_correct_axiom 1 4

theorem vasyuninBEntry_1_4_eval :
    ((((74098041/159590000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 4) ∧
    (vasyuninBEntry 1 4 ≤ (((74129959/159590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_14_formula_bound
  constructor <;> linarith

theorem G1_4_interval :
    ((((74098041/159590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 4) ∧
    (baezDuarteGramEntry 1 4 ≤ (((74129959/159590000) : ℚ) : ℝ)) := by
  rw [G1_4_formula]
  exact vasyuninBEntry_1_4_eval

def interval_1_4 : NamedVasyuninInterval :=
{
  h := 1
  k := 4
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_4_interval
}

theorem G1_5_formula : baezDuarteGramEntry 1 5 = vasyuninBEntry 1 5 := vasyuninBEntry_correct_axiom 1 5

theorem vasyuninBEntry_1_5_eval :
    ((((297474187/758130000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 5) ∧
    (vasyuninBEntry 1 5 ≤ (((297625813/758130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_15_formula_bound
  constructor <;> linarith

theorem G1_5_interval :
    ((((297474187/758130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 5) ∧
    (baezDuarteGramEntry 1 5 ≤ (((297625813/758130000) : ℚ) : ℝ)) := by
  rw [G1_5_formula]
  exact vasyuninBEntry_1_5_eval

def interval_1_5 : NamedVasyuninInterval :=
{
  h := 1
  k := 5
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_5_interval
}

theorem G1_6_formula : baezDuarteGramEntry 1 6 = vasyuninBEntry 1 6 := vasyuninBEntry_correct_axiom 1 6

theorem vasyuninBEntry_1_6_eval :
    ((((138189523/404770000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 6) ∧
    (vasyuninBEntry 1 6 ≤ (((138270477/404770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_16_formula_bound
  constructor <;> linarith

theorem G1_6_interval :
    ((((138189523/404770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 6) ∧
    (baezDuarteGramEntry 1 6 ≤ (((138270477/404770000) : ℚ) : ℝ)) := by
  rw [G1_6_formula]
  exact vasyuninBEntry_1_6_eval

def interval_1_6 : NamedVasyuninInterval :=
{
  h := 1
  k := 6
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_6_interval
}

theorem G1_7_formula : baezDuarteGramEntry 1 7 = vasyuninBEntry 1 7 := vasyuninBEntry_correct_axiom 1 7

theorem vasyuninBEntry_1_7_eval :
    ((((155428731/512690000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 7) ∧
    (vasyuninBEntry 1 7 ≤ (((155531269/512690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_17_formula_bound
  constructor <;> linarith

theorem G1_7_interval :
    ((((155428731/512690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 7) ∧
    (baezDuarteGramEntry 1 7 ≤ (((155531269/512690000) : ℚ) : ℝ)) := by
  rw [G1_7_formula]
  exact vasyuninBEntry_1_7_eval

def interval_1_7 : NamedVasyuninInterval :=
{
  h := 1
  k := 7
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_7_interval
}

theorem G1_8_formula : baezDuarteGramEntry 1 8 = vasyuninBEntry 1 8 := vasyuninBEntry_correct_axiom 1 8

theorem vasyuninBEntry_1_8_eval :
    ((((14952029/54710000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 8) ∧
    (vasyuninBEntry 1 8 ≤ (((14962971/54710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_18_formula_bound
  constructor <;> linarith

theorem G1_8_interval :
    ((((14952029/54710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 8) ∧
    (baezDuarteGramEntry 1 8 ≤ (((14962971/54710000) : ℚ) : ℝ)) := by
  rw [G1_8_formula]
  exact vasyuninBEntry_1_8_eval

def interval_1_8 : NamedVasyuninInterval :=
{
  h := 1
  k := 8
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_8_interval
}

theorem G1_9_formula : baezDuarteGramEntry 1 9 = vasyuninBEntry 1 9 := vasyuninBEntry_correct_axiom 1 9

theorem vasyuninBEntry_1_9_eval :
    ((((214204061/859390000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 9) ∧
    (vasyuninBEntry 1 9 ≤ (((214375939/859390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_19_formula_bound
  constructor <;> linarith

theorem G1_9_interval :
    ((((214204061/859390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 9) ∧
    (baezDuarteGramEntry 1 9 ≤ (((214375939/859390000) : ℚ) : ℝ)) := by
  rw [G1_9_formula]
  exact vasyuninBEntry_1_9_eval

def interval_1_9 : NamedVasyuninInterval :=
{
  h := 1
  k := 9
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_9_interval
}

theorem G1_10_formula : baezDuarteGramEntry 1 10 = vasyuninBEntry 1 10 := vasyuninBEntry_correct_axiom 1 10

theorem vasyuninBEntry_1_10_eval :
    ((((16135967/70330000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 10) ∧
    (vasyuninBEntry 1 10 ≤ (((16150033/70330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_110_formula_bound
  constructor <;> linarith

theorem G1_10_interval :
    ((((16135967/70330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 10) ∧
    (baezDuarteGramEntry 1 10 ≤ (((16150033/70330000) : ℚ) : ℝ)) := by
  rw [G1_10_formula]
  exact vasyuninBEntry_1_10_eval

def interval_1_10 : NamedVasyuninInterval :=
{
  h := 1
  k := 10
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_10_interval
}

theorem G2_1_formula : baezDuarteGramEntry 2 1 = vasyuninBEntry 1 2 := by
  rw [baezDuarteGramEntry_symm 2 1]
  exact G1_2_formula

theorem G2_1_interval :
    ((((3861/5000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 1) ∧
    (baezDuarteGramEntry 2 1 ≤ (((7723/10000) : ℚ) : ℝ)) := by
  rw [G2_1_formula]
  exact vasyuninBEntry_1_2_eval

def interval_2_1 : NamedVasyuninInterval :=
{
  h := 2
  k := 1
  lower := (3861/5000)
  upper := (7723/10000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_1_interval
}

theorem G2_2_formula_eq : baezDuarteGramEntry 2 2 = (1 / (2 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 2 := by norm_num
  rw [baez_duarte_diagonal_scaling 2 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G2_2_log_gamma_interval :
  ((((6303/10000) : ℚ) : ℝ) ≤ (1 / (2 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (2 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((394/625) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 2 (by norm_num)
  constructor
  · have : ((((6303/10000) : ℚ) : ℝ) ≤ (1 / (2 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (2 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((394/625) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G2_2_interval : ((((6303/10000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 2) ∧ (baezDuarteGramEntry 2 2 ≤ (((394/625) : ℚ) : ℝ)) := by
  rw [G2_2_formula_eq]
  exact G2_2_log_gamma_interval

def interval_2_2 : NamedVasyuninInterval :=
{
  h := 2
  k := 2
  lower := (6303/10000)
  upper := (394/625)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G2_2_interval
}

theorem G2_3_formula : baezDuarteGramEntry 2 3 = vasyuninBEntry 2 3 := vasyuninBEntry_correct_axiom 2 3

theorem vasyuninBEntry_2_3_eval :
    ((((4411/10000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 3) ∧
    (vasyuninBEntry 2 3 ≤ (((1103/2500) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_23_formula_bound
  constructor <;> linarith

theorem G2_3_interval :
    ((((4411/10000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 3) ∧
    (baezDuarteGramEntry 2 3 ≤ (((1103/2500) : ℚ) : ℝ)) := by
  rw [G2_3_formula]
  exact vasyuninBEntry_2_3_eval

def interval_2_3 : NamedVasyuninInterval :=
{
  h := 2
  k := 3
  lower := (4411/10000)
  upper := (1103/2500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_3_interval
}

theorem G2_4_formula : baezDuarteGramEntry 2 4 = vasyuninBEntry 2 4 := vasyuninBEntry_correct_axiom 2 4

theorem vasyuninBEntry_2_4_eval :
    ((((368854443/955570000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 4) ∧
    (vasyuninBEntry 2 4 ≤ (((369045557/955570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_4_interval :
    ((((368854443/955570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 4) ∧
    (baezDuarteGramEntry 2 4 ≤ (((369045557/955570000) : ℚ) : ℝ)) := by
  rw [G2_4_formula]
  exact vasyuninBEntry_2_4_eval

def interval_2_4 : NamedVasyuninInterval :=
{
  h := 2
  k := 4
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_4_interval
}

theorem G2_5_formula : baezDuarteGramEntry 2 5 = vasyuninBEntry 2 5 := vasyuninBEntry_correct_axiom 2 5

theorem vasyuninBEntry_2_5_eval :
    ((((36498461/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 5) ∧
    (vasyuninBEntry 2 5 ≤ (((36521539/115390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_25_formula_bound
  constructor <;> linarith

theorem G2_5_interval :
    ((((36498461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 5) ∧
    (baezDuarteGramEntry 2 5 ≤ (((36521539/115390000) : ℚ) : ℝ)) := by
  rw [G2_5_formula]
  exact vasyuninBEntry_2_5_eval

def interval_2_5 : NamedVasyuninInterval :=
{
  h := 2
  k := 5
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_5_interval
}

theorem G2_6_formula : baezDuarteGramEntry 2 6 = vasyuninBEntry 2 6 := vasyuninBEntry_correct_axiom 2 6

theorem vasyuninBEntry_2_6_eval :
    ((((269206331/936690000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 6) ∧
    (vasyuninBEntry 2 6 ≤ (((269393669/936690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_6_interval :
    ((((269206331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 6) ∧
    (baezDuarteGramEntry 2 6 ≤ (((269393669/936690000) : ℚ) : ℝ)) := by
  rw [G2_6_formula]
  exact vasyuninBEntry_2_6_eval

def interval_2_6 : NamedVasyuninInterval :=
{
  h := 2
  k := 6
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_6_interval
}

theorem G2_7_formula : baezDuarteGramEntry 2 7 = vasyuninBEntry 2 7 := vasyuninBEntry_correct_axiom 2 7

theorem vasyuninBEntry_2_7_eval :
    ((((157846907/630930000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 7) ∧
    (vasyuninBEntry 2 7 ≤ (((157973093/630930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_27_formula_bound
  constructor <;> linarith

theorem G2_7_interval :
    ((((157846907/630930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 7) ∧
    (baezDuarteGramEntry 2 7 ≤ (((157973093/630930000) : ℚ) : ℝ)) := by
  rw [G2_7_formula]
  exact vasyuninBEntry_2_7_eval

def interval_2_7 : NamedVasyuninInterval :=
{
  h := 2
  k := 7
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_7_interval
}

theorem G2_8_formula : baezDuarteGramEntry 2 8 = vasyuninBEntry 2 8 := vasyuninBEntry_correct_axiom 2 8

theorem vasyuninBEntry_2_8_eval :
    ((((75927287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 8) ∧
    (vasyuninBEntry 2 8 ≤ (((75992713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_8_interval :
    ((((75927287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 8) ∧
    (baezDuarteGramEntry 2 8 ≤ (((75992713/327130000) : ℚ) : ℝ)) := by
  rw [G2_8_formula]
  exact vasyuninBEntry_2_8_eval

def interval_2_8 : NamedVasyuninInterval :=
{
  h := 2
  k := 8
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_8_interval
}

theorem G2_9_formula : baezDuarteGramEntry 2 9 = vasyuninBEntry 2 9 := vasyuninBEntry_correct_axiom 2 9

theorem vasyuninBEntry_2_9_eval :
    ((((135824899/651010000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 9) ∧
    (vasyuninBEntry 2 9 ≤ (((135955101/651010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_29_formula_bound
  constructor <;> linarith

theorem G2_9_interval :
    ((((135824899/651010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 9) ∧
    (baezDuarteGramEntry 2 9 ≤ (((135955101/651010000) : ℚ) : ℝ)) := by
  rw [G2_9_formula]
  exact vasyuninBEntry_2_9_eval

def interval_2_9 : NamedVasyuninInterval :=
{
  h := 2
  k := 9
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_9_interval
}

theorem G2_10_formula : baezDuarteGramEntry 2 10 = vasyuninBEntry 2 10 := vasyuninBEntry_correct_axiom 2 10

theorem vasyuninBEntry_2_10_eval :
    ((((64257239/327610000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 10) ∧
    (vasyuninBEntry 2 10 ≤ (((64322761/327610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_10_interval :
    ((((64257239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 10) ∧
    (baezDuarteGramEntry 2 10 ≤ (((64322761/327610000) : ℚ) : ℝ)) := by
  rw [G2_10_formula]
  exact vasyuninBEntry_2_10_eval

def interval_2_10 : NamedVasyuninInterval :=
{
  h := 2
  k := 10
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_10_interval
}

theorem G3_1_formula : baezDuarteGramEntry 3 1 = vasyuninBEntry 1 3 := by
  rw [baezDuarteGramEntry_symm 3 1]
  exact G1_3_formula

theorem G3_1_interval :
    ((((23/40) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 1) ∧
    (baezDuarteGramEntry 3 1 ≤ (((5751/10000) : ℚ) : ℝ)) := by
  rw [G3_1_formula]
  exact vasyuninBEntry_1_3_eval

def interval_3_1 : NamedVasyuninInterval :=
{
  h := 3
  k := 1
  lower := (23/40)
  upper := (5751/10000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_1_interval
}

theorem G3_2_formula : baezDuarteGramEntry 3 2 = vasyuninBEntry 2 3 := by
  rw [baezDuarteGramEntry_symm 3 2]
  exact G2_3_formula

theorem G3_2_interval :
    ((((4411/10000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 2) ∧
    (baezDuarteGramEntry 3 2 ≤ (((1103/2500) : ℚ) : ℝ)) := by
  rw [G3_2_formula]
  exact vasyuninBEntry_2_3_eval

def interval_3_2 : NamedVasyuninInterval :=
{
  h := 3
  k := 2
  lower := (4411/10000)
  upper := (1103/2500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_2_interval
}

theorem G3_3_formula_eq : baezDuarteGramEntry 3 3 = (1 / (3 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 3 := by norm_num
  rw [baez_duarte_diagonal_scaling 3 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G3_3_log_gamma_interval :
  ((((2101/5000) : ℚ) : ℝ) ≤ (1 / (3 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (3 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((4203/10000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 3 (by norm_num)
  constructor
  · have : ((((2101/5000) : ℚ) : ℝ) ≤ (1 / (3 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (3 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((4203/10000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G3_3_interval : ((((2101/5000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 3) ∧ (baezDuarteGramEntry 3 3 ≤ (((4203/10000) : ℚ) : ℝ)) := by
  rw [G3_3_formula_eq]
  exact G3_3_log_gamma_interval

def interval_3_3 : NamedVasyuninInterval :=
{
  h := 3
  k := 3
  lower := (2101/5000)
  upper := (4203/10000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G3_3_interval
}

theorem G3_4_formula : baezDuarteGramEntry 3 4 = vasyuninBEntry 3 4 := vasyuninBEntry_correct_axiom 3 4

theorem vasyuninBEntry_3_4_eval :
    ((((12635993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 4) ∧
    (vasyuninBEntry 3 4 ≤ (((12644007/40070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_34_formula_bound
  constructor <;> linarith

theorem G3_4_interval :
    ((((12635993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 4) ∧
    (baezDuarteGramEntry 3 4 ≤ (((12644007/40070000) : ℚ) : ℝ)) := by
  rw [G3_4_formula]
  exact vasyuninBEntry_3_4_eval

def interval_3_4 : NamedVasyuninInterval :=
{
  h := 3
  k := 4
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_4_interval
}

theorem G3_5_formula : baezDuarteGramEntry 3 5 = vasyuninBEntry 3 5 := vasyuninBEntry_correct_axiom 3 5

theorem vasyuninBEntry_3_5_eval :
    ((((80650507/294930000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 5) ∧
    (vasyuninBEntry 3 5 ≤ (((80709493/294930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_35_formula_bound
  constructor <;> linarith

theorem G3_5_interval :
    ((((80650507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 5) ∧
    (baezDuarteGramEntry 3 5 ≤ (((80709493/294930000) : ℚ) : ℝ)) := by
  rw [G3_5_formula]
  exact vasyuninBEntry_3_5_eval

def interval_3_5 : NamedVasyuninInterval :=
{
  h := 3
  k := 5
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_5_interval
}

theorem G3_6_formula : baezDuarteGramEntry 3 6 = vasyuninBEntry 3 6 := vasyuninBEntry_correct_axiom 3 6

theorem vasyuninBEntry_3_6_eval :
    ((((45200433/175670000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 6) ∧
    (vasyuninBEntry 3 6 ≤ (((45235567/175670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_6_interval :
    ((((45200433/175670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 6) ∧
    (baezDuarteGramEntry 3 6 ≤ (((45235567/175670000) : ℚ) : ℝ)) := by
  rw [G3_6_formula]
  exact vasyuninBEntry_3_6_eval

def interval_3_6 : NamedVasyuninInterval :=
{
  h := 3
  k := 6
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_6_interval
}

theorem G3_7_formula : baezDuarteGramEntry 3 7 = vasyuninBEntry 3 7 := vasyuninBEntry_correct_axiom 3 7

theorem vasyuninBEntry_3_7_eval :
    ((((112519007/509930000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 7) ∧
    (vasyuninBEntry 3 7 ≤ (((112620993/509930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_37_formula_bound
  constructor <;> linarith

theorem G3_7_interval :
    ((((112519007/509930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 7) ∧
    (baezDuarteGramEntry 3 7 ≤ (((112620993/509930000) : ℚ) : ℝ)) := by
  rw [G3_7_formula]
  exact vasyuninBEntry_3_7_eval

def interval_3_7 : NamedVasyuninInterval :=
{
  h := 3
  k := 7
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_7_interval
}

theorem G3_8_formula : baezDuarteGramEntry 3 8 = vasyuninBEntry 3 8 := vasyuninBEntry_correct_axiom 3 8

theorem vasyuninBEntry_3_8_eval :
    ((((4014879/19960000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 8) ∧
    (vasyuninBEntry 3 8 ≤ (((4018871/19960000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_38_formula_bound
  constructor <;> linarith

theorem G3_8_interval :
    ((((4014879/19960000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 8) ∧
    (baezDuarteGramEntry 3 8 ≤ (((4018871/19960000) : ℚ) : ℝ)) := by
  rw [G3_8_formula]
  exact vasyuninBEntry_3_8_eval

def interval_3_8 : NamedVasyuninInterval :=
{
  h := 3
  k := 8
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_8_interval
}

theorem G3_9_formula : baezDuarteGramEntry 3 9 = vasyuninBEntry 3 9 := vasyuninBEntry_correct_axiom 3 9

theorem vasyuninBEntry_3_9_eval :
    ((((124245143/648570000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 9) ∧
    (vasyuninBEntry 3 9 ≤ (((124374857/648570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_9_interval :
    ((((124245143/648570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 9) ∧
    (baezDuarteGramEntry 3 9 ≤ (((124374857/648570000) : ℚ) : ℝ)) := by
  rw [G3_9_formula]
  exact vasyuninBEntry_3_9_eval

def interval_3_9 : NamedVasyuninInterval :=
{
  h := 3
  k := 9
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_9_interval
}

theorem G3_10_formula : baezDuarteGramEntry 3 10 = vasyuninBEntry 3 10 := vasyuninBEntry_correct_axiom 3 10

theorem vasyuninBEntry_3_10_eval :
    ((((64452631/373690000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 10) ∧
    (vasyuninBEntry 3 10 ≤ (((64527369/373690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_310_formula_bound
  constructor <;> linarith

theorem G3_10_interval :
    ((((64452631/373690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 10) ∧
    (baezDuarteGramEntry 3 10 ≤ (((64527369/373690000) : ℚ) : ℝ)) := by
  rw [G3_10_formula]
  exact vasyuninBEntry_3_10_eval

def interval_3_10 : NamedVasyuninInterval :=
{
  h := 3
  k := 10
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_10_interval
}

theorem G4_1_formula : baezDuarteGramEntry 4 1 = vasyuninBEntry 1 4 := by
  rw [baezDuarteGramEntry_symm 4 1]
  exact G1_4_formula

theorem G4_1_interval :
    ((((74098041/159590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 1) ∧
    (baezDuarteGramEntry 4 1 ≤ (((74129959/159590000) : ℚ) : ℝ)) := by
  rw [G4_1_formula]
  exact vasyuninBEntry_1_4_eval

def interval_4_1 : NamedVasyuninInterval :=
{
  h := 4
  k := 1
  lower := (74098041/159590000)
  upper := (74129959/159590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_1_interval
}

theorem G4_2_formula : baezDuarteGramEntry 4 2 = vasyuninBEntry 2 4 := by
  rw [baezDuarteGramEntry_symm 4 2]
  exact G2_4_formula

theorem G4_2_interval :
    ((((368854443/955570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 2) ∧
    (baezDuarteGramEntry 4 2 ≤ (((369045557/955570000) : ℚ) : ℝ)) := by
  rw [G4_2_formula]
  exact vasyuninBEntry_2_4_eval

def interval_4_2 : NamedVasyuninInterval :=
{
  h := 4
  k := 2
  lower := (368854443/955570000)
  upper := (369045557/955570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_2_interval
}

theorem G4_3_formula : baezDuarteGramEntry 4 3 = vasyuninBEntry 3 4 := by
  rw [baezDuarteGramEntry_symm 4 3]
  exact G3_4_formula

theorem G4_3_interval :
    ((((12635993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 3) ∧
    (baezDuarteGramEntry 4 3 ≤ (((12644007/40070000) : ℚ) : ℝ)) := by
  rw [G4_3_formula]
  exact vasyuninBEntry_3_4_eval

def interval_4_3 : NamedVasyuninInterval :=
{
  h := 4
  k := 3
  lower := (12635993/40070000)
  upper := (12644007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_3_interval
}

theorem G4_4_formula_eq : baezDuarteGramEntry 4 4 = (1 / (4 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 4 := by norm_num
  rw [baez_duarte_diagonal_scaling 4 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G4_4_log_gamma_interval :
  ((((797903/2532500) : ℚ) : ℝ) ≤ (1 / (4 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (4 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((1596819/5065000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 4 (by norm_num)
  constructor
  · have : ((((797903/2532500) : ℚ) : ℝ) ≤ (1 / (4 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (4 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((1596819/5065000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G4_4_interval : ((((797903/2532500) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 4) ∧ (baezDuarteGramEntry 4 4 ≤ (((1596819/5065000) : ℚ) : ℝ)) := by
  rw [G4_4_formula_eq]
  exact G4_4_log_gamma_interval

def interval_4_4 : NamedVasyuninInterval :=
{
  h := 4
  k := 4
  lower := (797903/2532500)
  upper := (1596819/5065000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G4_4_interval
}

theorem G4_5_formula : baezDuarteGramEntry 4 5 = vasyuninBEntry 4 5 := vasyuninBEntry_correct_axiom 4 5

theorem vasyuninBEntry_4_5_eval :
    ((((25442211/102890000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 5) ∧
    (vasyuninBEntry 4 5 ≤ (((25462789/102890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_45_formula_bound
  constructor <;> linarith

theorem G4_5_interval :
    ((((25442211/102890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 5) ∧
    (baezDuarteGramEntry 4 5 ≤ (((25462789/102890000) : ℚ) : ℝ)) := by
  rw [G4_5_formula]
  exact vasyuninBEntry_4_5_eval

def interval_4_5 : NamedVasyuninInterval :=
{
  h := 4
  k := 5
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_5_interval
}

theorem G4_6_formula : baezDuarteGramEntry 4 6 = vasyuninBEntry 4 6 := vasyuninBEntry_correct_axiom 4 6

theorem vasyuninBEntry_4_6_eval :
    ((((55097507/249930000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 6) ∧
    (vasyuninBEntry 4 6 ≤ (((55147493/249930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_6_interval :
    ((((55097507/249930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 6) ∧
    (baezDuarteGramEntry 4 6 ≤ (((55147493/249930000) : ℚ) : ℝ)) := by
  rw [G4_6_formula]
  exact vasyuninBEntry_4_6_eval

def interval_4_6 : NamedVasyuninInterval :=
{
  h := 4
  k := 6
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_6_interval
}

theorem G4_7_formula : baezDuarteGramEntry 4 7 = vasyuninBEntry 4 7 := vasyuninBEntry_correct_axiom 4 7

theorem vasyuninBEntry_4_7_eval :
    ((((49395219/247810000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 7) ∧
    (vasyuninBEntry 4 7 ≤ (((49444781/247810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_47_formula_bound
  constructor <;> linarith

theorem G4_7_interval :
    ((((49395219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 7) ∧
    (baezDuarteGramEntry 4 7 ≤ (((49444781/247810000) : ℚ) : ℝ)) := by
  rw [G4_7_formula]
  exact vasyuninBEntry_4_7_eval

def interval_4_7 : NamedVasyuninInterval :=
{
  h := 4
  k := 7
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_7_interval
}

theorem G4_8_formula : baezDuarteGramEntry 4 8 = vasyuninBEntry 4 8 := vasyuninBEntry_correct_axiom 4 8

theorem vasyuninBEntry_4_8_eval :
    ((((14052717/72830000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 8) ∧
    (vasyuninBEntry 4 8 ≤ (((14067283/72830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_8_interval :
    ((((14052717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 8) ∧
    (baezDuarteGramEntry 4 8 ≤ (((14067283/72830000) : ℚ) : ℝ)) := by
  rw [G4_8_formula]
  exact vasyuninBEntry_4_8_eval

def interval_4_8 : NamedVasyuninInterval :=
{
  h := 4
  k := 8
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_8_interval
}

theorem G4_9_formula : baezDuarteGramEntry 4 9 = vasyuninBEntry 4 9 := vasyuninBEntry_correct_axiom 4 9

theorem vasyuninBEntry_4_9_eval :
    ((((163044103/958970000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 9) ∧
    (vasyuninBEntry 4 9 ≤ (((163235897/958970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_49_formula_bound
  constructor <;> linarith

theorem G4_9_interval :
    ((((163044103/958970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 9) ∧
    (baezDuarteGramEntry 4 9 ≤ (((163235897/958970000) : ℚ) : ℝ)) := by
  rw [G4_9_formula]
  exact vasyuninBEntry_4_9_eval

def interval_4_9 : NamedVasyuninInterval :=
{
  h := 4
  k := 9
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_9_interval
}

theorem G4_10_formula : baezDuarteGramEntry 4 10 = vasyuninBEntry 4 10 := vasyuninBEntry_correct_axiom 4 10

theorem vasyuninBEntry_4_10_eval :
    ((((18243461/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 10) ∧
    (vasyuninBEntry 4 10 ≤ (((18266539/115390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_10_interval :
    ((((18243461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 10) ∧
    (baezDuarteGramEntry 4 10 ≤ (((18266539/115390000) : ℚ) : ℝ)) := by
  rw [G4_10_formula]
  exact vasyuninBEntry_4_10_eval

def interval_4_10 : NamedVasyuninInterval :=
{
  h := 4
  k := 10
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_10_interval
}

theorem G5_1_formula : baezDuarteGramEntry 5 1 = vasyuninBEntry 1 5 := by
  rw [baezDuarteGramEntry_symm 5 1]
  exact G1_5_formula

theorem G5_1_interval :
    ((((297474187/758130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 1) ∧
    (baezDuarteGramEntry 5 1 ≤ (((297625813/758130000) : ℚ) : ℝ)) := by
  rw [G5_1_formula]
  exact vasyuninBEntry_1_5_eval

def interval_5_1 : NamedVasyuninInterval :=
{
  h := 5
  k := 1
  lower := (297474187/758130000)
  upper := (297625813/758130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_1_interval
}

theorem G5_2_formula : baezDuarteGramEntry 5 2 = vasyuninBEntry 2 5 := by
  rw [baezDuarteGramEntry_symm 5 2]
  exact G2_5_formula

theorem G5_2_interval :
    ((((36498461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 2) ∧
    (baezDuarteGramEntry 5 2 ≤ (((36521539/115390000) : ℚ) : ℝ)) := by
  rw [G5_2_formula]
  exact vasyuninBEntry_2_5_eval

def interval_5_2 : NamedVasyuninInterval :=
{
  h := 5
  k := 2
  lower := (36498461/115390000)
  upper := (36521539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_2_interval
}

theorem G5_3_formula : baezDuarteGramEntry 5 3 = vasyuninBEntry 3 5 := by
  rw [baezDuarteGramEntry_symm 5 3]
  exact G3_5_formula

theorem G5_3_interval :
    ((((80650507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 3) ∧
    (baezDuarteGramEntry 5 3 ≤ (((80709493/294930000) : ℚ) : ℝ)) := by
  rw [G5_3_formula]
  exact vasyuninBEntry_3_5_eval

def interval_5_3 : NamedVasyuninInterval :=
{
  h := 5
  k := 3
  lower := (80650507/294930000)
  upper := (80709493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_3_interval
}

theorem G5_4_formula : baezDuarteGramEntry 5 4 = vasyuninBEntry 4 5 := by
  rw [baezDuarteGramEntry_symm 5 4]
  exact G4_5_formula

theorem G5_4_interval :
    ((((25442211/102890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 4) ∧
    (baezDuarteGramEntry 5 4 ≤ (((25462789/102890000) : ℚ) : ℝ)) := by
  rw [G5_4_formula]
  exact vasyuninBEntry_4_5_eval

def interval_5_4 : NamedVasyuninInterval :=
{
  h := 5
  k := 4
  lower := (25442211/102890000)
  upper := (25462789/102890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_4_interval
}

theorem G5_5_formula_eq : baezDuarteGramEntry 5 5 = (1 / (5 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 5 := by norm_num
  rw [baez_duarte_diagonal_scaling 5 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G5_5_log_gamma_interval :
  ((((175820239/697610000) : ℚ) : ℝ) ≤ (1 / (5 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (5 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((175959761/697610000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 5 (by norm_num)
  constructor
  · have : ((((175820239/697610000) : ℚ) : ℝ) ≤ (1 / (5 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (5 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((175959761/697610000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G5_5_interval : ((((175820239/697610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 5) ∧ (baezDuarteGramEntry 5 5 ≤ (((175959761/697610000) : ℚ) : ℝ)) := by
  rw [G5_5_formula_eq]
  exact G5_5_log_gamma_interval

def interval_5_5 : NamedVasyuninInterval :=
{
  h := 5
  k := 5
  lower := (175820239/697610000)
  upper := (175959761/697610000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G5_5_interval
}

theorem G5_6_formula : baezDuarteGramEntry 5 6 = vasyuninBEntry 5 6 := vasyuninBEntry_correct_axiom 5 6

theorem vasyuninBEntry_5_6_eval :
    ((((34982859/171410000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 6) ∧
    (vasyuninBEntry 5 6 ≤ (((35017141/171410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_56_formula_bound
  constructor <;> linarith

theorem G5_6_interval :
    ((((34982859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 6) ∧
    (baezDuarteGramEntry 5 6 ≤ (((35017141/171410000) : ℚ) : ℝ)) := by
  rw [G5_6_formula]
  exact vasyuninBEntry_5_6_eval

def interval_5_6 : NamedVasyuninInterval :=
{
  h := 5
  k := 6
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_6_interval
}

theorem G5_7_formula : baezDuarteGramEntry 5 7 = vasyuninBEntry 5 7 := vasyuninBEntry_correct_axiom 5 7

theorem vasyuninBEntry_5_7_eval :
    ((((167378283/917170000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 7) ∧
    (vasyuninBEntry 5 7 ≤ (((167561717/917170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_57_formula_bound
  constructor <;> linarith

theorem G5_7_interval :
    ((((167378283/917170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 7) ∧
    (baezDuarteGramEntry 5 7 ≤ (((167561717/917170000) : ℚ) : ℝ)) := by
  rw [G5_7_formula]
  exact vasyuninBEntry_5_7_eval

def interval_5_7 : NamedVasyuninInterval :=
{
  h := 5
  k := 7
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_7_interval
}

theorem G5_8_formula : baezDuarteGramEntry 5 8 = vasyuninBEntry 5 8 := vasyuninBEntry_correct_axiom 5 8

theorem vasyuninBEntry_5_8_eval :
    ((((2514001/14990000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 8) ∧
    (vasyuninBEntry 5 8 ≤ (((2516999/14990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_58_formula_bound
  constructor <;> linarith

theorem G5_8_interval :
    ((((2514001/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 8) ∧
    (baezDuarteGramEntry 5 8 ≤ (((2516999/14990000) : ℚ) : ℝ)) := by
  rw [G5_8_formula]
  exact vasyuninBEntry_5_8_eval

def interval_5_8 : NamedVasyuninInterval :=
{
  h := 5
  k := 8
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_8_interval
}

theorem G5_9_formula : baezDuarteGramEntry 5 9 = vasyuninBEntry 5 9 := vasyuninBEntry_correct_axiom 5 9

theorem vasyuninBEntry_5_9_eval :
    ((((17229039/109610000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 9) ∧
    (vasyuninBEntry 5 9 ≤ (((17250961/109610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_59_formula_bound
  constructor <;> linarith

theorem G5_9_interval :
    ((((17229039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 9) ∧
    (baezDuarteGramEntry 5 9 ≤ (((17250961/109610000) : ℚ) : ℝ)) := by
  rw [G5_9_formula]
  exact vasyuninBEntry_5_9_eval

def interval_5_9 : NamedVasyuninInterval :=
{
  h := 5
  k := 9
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_9_interval
}

theorem G5_10_formula : baezDuarteGramEntry 5 10 = vasyuninBEntry 5 10 := vasyuninBEntry_correct_axiom 5 10

theorem vasyuninBEntry_5_10_eval :
    ((((50922007/329930000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 10) ∧
    (vasyuninBEntry 5 10 ≤ (((50987993/329930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_10_interval :
    ((((50922007/329930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 10) ∧
    (baezDuarteGramEntry 5 10 ≤ (((50987993/329930000) : ℚ) : ℝ)) := by
  rw [G5_10_formula]
  exact vasyuninBEntry_5_10_eval

def interval_5_10 : NamedVasyuninInterval :=
{
  h := 5
  k := 10
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_10_interval
}

theorem G6_1_formula : baezDuarteGramEntry 6 1 = vasyuninBEntry 1 6 := by
  rw [baezDuarteGramEntry_symm 6 1]
  exact G1_6_formula

theorem G6_1_interval :
    ((((138189523/404770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 1) ∧
    (baezDuarteGramEntry 6 1 ≤ (((138270477/404770000) : ℚ) : ℝ)) := by
  rw [G6_1_formula]
  exact vasyuninBEntry_1_6_eval

def interval_6_1 : NamedVasyuninInterval :=
{
  h := 6
  k := 1
  lower := (138189523/404770000)
  upper := (138270477/404770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_1_interval
}

theorem G6_2_formula : baezDuarteGramEntry 6 2 = vasyuninBEntry 2 6 := by
  rw [baezDuarteGramEntry_symm 6 2]
  exact G2_6_formula

theorem G6_2_interval :
    ((((269206331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 2) ∧
    (baezDuarteGramEntry 6 2 ≤ (((269393669/936690000) : ℚ) : ℝ)) := by
  rw [G6_2_formula]
  exact vasyuninBEntry_2_6_eval

def interval_6_2 : NamedVasyuninInterval :=
{
  h := 6
  k := 2
  lower := (269206331/936690000)
  upper := (269393669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_2_interval
}

theorem G6_3_formula : baezDuarteGramEntry 6 3 = vasyuninBEntry 3 6 := by
  rw [baezDuarteGramEntry_symm 6 3]
  exact G3_6_formula

theorem G6_3_interval :
    ((((45200433/175670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 3) ∧
    (baezDuarteGramEntry 6 3 ≤ (((45235567/175670000) : ℚ) : ℝ)) := by
  rw [G6_3_formula]
  exact vasyuninBEntry_3_6_eval

def interval_6_3 : NamedVasyuninInterval :=
{
  h := 6
  k := 3
  lower := (45200433/175670000)
  upper := (45235567/175670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_3_interval
}

theorem G6_4_formula : baezDuarteGramEntry 6 4 = vasyuninBEntry 4 6 := by
  rw [baezDuarteGramEntry_symm 6 4]
  exact G4_6_formula

theorem G6_4_interval :
    ((((55097507/249930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 4) ∧
    (baezDuarteGramEntry 6 4 ≤ (((55147493/249930000) : ℚ) : ℝ)) := by
  rw [G6_4_formula]
  exact vasyuninBEntry_4_6_eval

def interval_6_4 : NamedVasyuninInterval :=
{
  h := 6
  k := 4
  lower := (55097507/249930000)
  upper := (55147493/249930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_4_interval
}

theorem G6_5_formula : baezDuarteGramEntry 6 5 = vasyuninBEntry 5 6 := by
  rw [baezDuarteGramEntry_symm 6 5]
  exact G5_6_formula

theorem G6_5_interval :
    ((((34982859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 5) ∧
    (baezDuarteGramEntry 6 5 ≤ (((35017141/171410000) : ℚ) : ℝ)) := by
  rw [G6_5_formula]
  exact vasyuninBEntry_5_6_eval

def interval_6_5 : NamedVasyuninInterval :=
{
  h := 6
  k := 5
  lower := (34982859/171410000)
  upper := (35017141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_5_interval
}

theorem G6_6_formula_eq : baezDuarteGramEntry 6 6 = (1 / (6 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 6 := by norm_num
  rw [baez_duarte_diagonal_scaling 6 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G6_6_log_gamma_interval :
  ((((198705383/946170000) : ℚ) : ℝ) ≤ (1 / (6 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (6 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((198894617/946170000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 6 (by norm_num)
  constructor
  · have : ((((198705383/946170000) : ℚ) : ℝ) ≤ (1 / (6 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (6 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((198894617/946170000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G6_6_interval : ((((198705383/946170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 6) ∧ (baezDuarteGramEntry 6 6 ≤ (((198894617/946170000) : ℚ) : ℝ)) := by
  rw [G6_6_formula_eq]
  exact G6_6_log_gamma_interval

def interval_6_6 : NamedVasyuninInterval :=
{
  h := 6
  k := 6
  lower := (198705383/946170000)
  upper := (198894617/946170000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G6_6_interval
}

theorem G6_7_formula : baezDuarteGramEntry 6 7 = vasyuninBEntry 6 7 := vasyuninBEntry_correct_axiom 6 7

theorem vasyuninBEntry_6_7_eval :
    ((((81713059/469410000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 7) ∧
    (vasyuninBEntry 6 7 ≤ (((81806941/469410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_67_formula_bound
  constructor <;> linarith

theorem G6_7_interval :
    ((((81713059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 7) ∧
    (baezDuarteGramEntry 6 7 ≤ (((81806941/469410000) : ℚ) : ℝ)) := by
  rw [G6_7_formula]
  exact vasyuninBEntry_6_7_eval

def interval_6_7 : NamedVasyuninInterval :=
{
  h := 6
  k := 7
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_7_interval
}

theorem G6_8_formula : baezDuarteGramEntry 6 8 = vasyuninBEntry 6 8 := vasyuninBEntry_correct_axiom 6 8

theorem vasyuninBEntry_6_8_eval :
    ((((6315993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 8) ∧
    (vasyuninBEntry 6 8 ≤ (((6324007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_8_interval :
    ((((6315993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 8) ∧
    (baezDuarteGramEntry 6 8 ≤ (((6324007/40070000) : ℚ) : ℝ)) := by
  rw [G6_8_formula]
  exact vasyuninBEntry_6_8_eval

def interval_6_8 : NamedVasyuninInterval :=
{
  h := 6
  k := 8
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_8_interval
}

theorem G6_9_formula : baezDuarteGramEntry 6 9 = vasyuninBEntry 6 9 := vasyuninBEntry_correct_axiom 6 9

theorem vasyuninBEntry_6_9_eval :
    ((((71076627/483730000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 9) ∧
    (vasyuninBEntry 6 9 ≤ (((71173373/483730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G6_9_interval :
    ((((71076627/483730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 9) ∧
    (baezDuarteGramEntry 6 9 ≤ (((71173373/483730000) : ℚ) : ℝ)) := by
  rw [G6_9_formula]
  exact vasyuninBEntry_6_9_eval

def interval_6_9 : NamedVasyuninInterval :=
{
  h := 6
  k := 9
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_9_interval
}

theorem G6_10_formula : baezDuarteGramEntry 6 10 = vasyuninBEntry 6 10 := vasyuninBEntry_correct_axiom 6 10

theorem vasyuninBEntry_6_10_eval :
    ((((40310507/294930000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 10) ∧
    (vasyuninBEntry 6 10 ≤ (((40369493/294930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_10_interval :
    ((((40310507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 10) ∧
    (baezDuarteGramEntry 6 10 ≤ (((40369493/294930000) : ℚ) : ℝ)) := by
  rw [G6_10_formula]
  exact vasyuninBEntry_6_10_eval

def interval_6_10 : NamedVasyuninInterval :=
{
  h := 6
  k := 10
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_10_interval
}

theorem G7_1_formula : baezDuarteGramEntry 7 1 = vasyuninBEntry 1 7 := by
  rw [baezDuarteGramEntry_symm 7 1]
  exact G1_7_formula

theorem G7_1_interval :
    ((((155428731/512690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 1) ∧
    (baezDuarteGramEntry 7 1 ≤ (((155531269/512690000) : ℚ) : ℝ)) := by
  rw [G7_1_formula]
  exact vasyuninBEntry_1_7_eval

def interval_7_1 : NamedVasyuninInterval :=
{
  h := 7
  k := 1
  lower := (155428731/512690000)
  upper := (155531269/512690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_1_interval
}

theorem G7_2_formula : baezDuarteGramEntry 7 2 = vasyuninBEntry 2 7 := by
  rw [baezDuarteGramEntry_symm 7 2]
  exact G2_7_formula

theorem G7_2_interval :
    ((((157846907/630930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 2) ∧
    (baezDuarteGramEntry 7 2 ≤ (((157973093/630930000) : ℚ) : ℝ)) := by
  rw [G7_2_formula]
  exact vasyuninBEntry_2_7_eval

def interval_7_2 : NamedVasyuninInterval :=
{
  h := 7
  k := 2
  lower := (157846907/630930000)
  upper := (157973093/630930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_2_interval
}

theorem G7_3_formula : baezDuarteGramEntry 7 3 = vasyuninBEntry 3 7 := by
  rw [baezDuarteGramEntry_symm 7 3]
  exact G3_7_formula

theorem G7_3_interval :
    ((((112519007/509930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 3) ∧
    (baezDuarteGramEntry 7 3 ≤ (((112620993/509930000) : ℚ) : ℝ)) := by
  rw [G7_3_formula]
  exact vasyuninBEntry_3_7_eval

def interval_7_3 : NamedVasyuninInterval :=
{
  h := 7
  k := 3
  lower := (112519007/509930000)
  upper := (112620993/509930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_3_interval
}

theorem G7_4_formula : baezDuarteGramEntry 7 4 = vasyuninBEntry 4 7 := by
  rw [baezDuarteGramEntry_symm 7 4]
  exact G4_7_formula

theorem G7_4_interval :
    ((((49395219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 4) ∧
    (baezDuarteGramEntry 7 4 ≤ (((49444781/247810000) : ℚ) : ℝ)) := by
  rw [G7_4_formula]
  exact vasyuninBEntry_4_7_eval

def interval_7_4 : NamedVasyuninInterval :=
{
  h := 7
  k := 4
  lower := (49395219/247810000)
  upper := (49444781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_4_interval
}

theorem G7_5_formula : baezDuarteGramEntry 7 5 = vasyuninBEntry 5 7 := by
  rw [baezDuarteGramEntry_symm 7 5]
  exact G5_7_formula

theorem G7_5_interval :
    ((((167378283/917170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 5) ∧
    (baezDuarteGramEntry 7 5 ≤ (((167561717/917170000) : ℚ) : ℝ)) := by
  rw [G7_5_formula]
  exact vasyuninBEntry_5_7_eval

def interval_7_5 : NamedVasyuninInterval :=
{
  h := 7
  k := 5
  lower := (167378283/917170000)
  upper := (167561717/917170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_5_interval
}

theorem G7_6_formula : baezDuarteGramEntry 7 6 = vasyuninBEntry 6 7 := by
  rw [baezDuarteGramEntry_symm 7 6]
  exact G6_7_formula

theorem G7_6_interval :
    ((((81713059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 6) ∧
    (baezDuarteGramEntry 7 6 ≤ (((81806941/469410000) : ℚ) : ℝ)) := by
  rw [G7_6_formula]
  exact vasyuninBEntry_6_7_eval

def interval_7_6 : NamedVasyuninInterval :=
{
  h := 7
  k := 6
  lower := (81713059/469410000)
  upper := (81806941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_6_interval
}

theorem G7_7_formula_eq : baezDuarteGramEntry 7 7 = (1 / (7 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 7 := by norm_num
  rw [baez_duarte_diagonal_scaling 7 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G7_7_log_gamma_interval :
  ((((70865629/393710000) : ℚ) : ℝ) ≤ (1 / (7 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (7 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((70944371/393710000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 7 (by norm_num)
  constructor
  · have : ((((70865629/393710000) : ℚ) : ℝ) ≤ (1 / (7 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (7 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((70944371/393710000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G7_7_interval : ((((70865629/393710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 7) ∧ (baezDuarteGramEntry 7 7 ≤ (((70944371/393710000) : ℚ) : ℝ)) := by
  rw [G7_7_formula_eq]
  exact G7_7_log_gamma_interval

def interval_7_7 : NamedVasyuninInterval :=
{
  h := 7
  k := 7
  lower := (70865629/393710000)
  upper := (70944371/393710000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G7_7_interval
}

theorem G7_8_formula : baezDuarteGramEntry 7 8 = vasyuninBEntry 7 8 := vasyuninBEntry_correct_axiom 7 8

theorem vasyuninBEntry_7_8_eval :
    ((((27455929/180710000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 8) ∧
    (vasyuninBEntry 7 8 ≤ (((27492071/180710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_78_formula_bound
  constructor <;> linarith

theorem G7_8_interval :
    ((((27455929/180710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 8) ∧
    (baezDuarteGramEntry 7 8 ≤ (((27492071/180710000) : ℚ) : ℝ)) := by
  rw [G7_8_formula]
  exact vasyuninBEntry_7_8_eval

def interval_7_8 : NamedVasyuninInterval :=
{
  h := 7
  k := 8
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_8_interval
}

theorem G7_9_formula : baezDuarteGramEntry 7 9 = vasyuninBEntry 7 9 := vasyuninBEntry_correct_axiom 7 9

theorem vasyuninBEntry_7_9_eval :
    ((((34032863/246370000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 9) ∧
    (vasyuninBEntry 7 9 ≤ (((34082137/246370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_79_formula_bound
  constructor <;> linarith

theorem G7_9_interval :
    ((((34032863/246370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 9) ∧
    (baezDuarteGramEntry 7 9 ≤ (((34082137/246370000) : ℚ) : ℝ)) := by
  rw [G7_9_formula]
  exact vasyuninBEntry_7_9_eval

def interval_7_9 : NamedVasyuninInterval :=
{
  h := 7
  k := 9
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_9_interval
}

theorem G7_10_formula : baezDuarteGramEntry 7 10 = vasyuninBEntry 7 10 := vasyuninBEntry_correct_axiom 7 10

theorem vasyuninBEntry_7_10_eval :
    ((((86672617/673830000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 10) ∧
    (vasyuninBEntry 7 10 ≤ (((86807383/673830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_710_formula_bound
  constructor <;> linarith

theorem G7_10_interval :
    ((((86672617/673830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 10) ∧
    (baezDuarteGramEntry 7 10 ≤ (((86807383/673830000) : ℚ) : ℝ)) := by
  rw [G7_10_formula]
  exact vasyuninBEntry_7_10_eval

def interval_7_10 : NamedVasyuninInterval :=
{
  h := 7
  k := 10
  lower := (86672617/673830000)
  upper := (86807383/673830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_10_interval
}

theorem G8_1_formula : baezDuarteGramEntry 8 1 = vasyuninBEntry 1 8 := by
  rw [baezDuarteGramEntry_symm 8 1]
  exact G1_8_formula

theorem G8_1_interval :
    ((((14952029/54710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 1) ∧
    (baezDuarteGramEntry 8 1 ≤ (((14962971/54710000) : ℚ) : ℝ)) := by
  rw [G8_1_formula]
  exact vasyuninBEntry_1_8_eval

def interval_8_1 : NamedVasyuninInterval :=
{
  h := 8
  k := 1
  lower := (14952029/54710000)
  upper := (14962971/54710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_1_interval
}

theorem G8_2_formula : baezDuarteGramEntry 8 2 = vasyuninBEntry 2 8 := by
  rw [baezDuarteGramEntry_symm 8 2]
  exact G2_8_formula

theorem G8_2_interval :
    ((((75927287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 2) ∧
    (baezDuarteGramEntry 8 2 ≤ (((75992713/327130000) : ℚ) : ℝ)) := by
  rw [G8_2_formula]
  exact vasyuninBEntry_2_8_eval

def interval_8_2 : NamedVasyuninInterval :=
{
  h := 8
  k := 2
  lower := (75927287/327130000)
  upper := (75992713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_2_interval
}

theorem G8_3_formula : baezDuarteGramEntry 8 3 = vasyuninBEntry 3 8 := by
  rw [baezDuarteGramEntry_symm 8 3]
  exact G3_8_formula

theorem G8_3_interval :
    ((((4014879/19960000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 3) ∧
    (baezDuarteGramEntry 8 3 ≤ (((4018871/19960000) : ℚ) : ℝ)) := by
  rw [G8_3_formula]
  exact vasyuninBEntry_3_8_eval

def interval_8_3 : NamedVasyuninInterval :=
{
  h := 8
  k := 3
  lower := (4014879/19960000)
  upper := (4018871/19960000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_3_interval
}

theorem G8_4_formula : baezDuarteGramEntry 8 4 = vasyuninBEntry 4 8 := by
  rw [baezDuarteGramEntry_symm 8 4]
  exact G4_8_formula

theorem G8_4_interval :
    ((((14052717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 4) ∧
    (baezDuarteGramEntry 8 4 ≤ (((14067283/72830000) : ℚ) : ℝ)) := by
  rw [G8_4_formula]
  exact vasyuninBEntry_4_8_eval

def interval_8_4 : NamedVasyuninInterval :=
{
  h := 8
  k := 4
  lower := (14052717/72830000)
  upper := (14067283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_4_interval
}

theorem G8_5_formula : baezDuarteGramEntry 8 5 = vasyuninBEntry 5 8 := by
  rw [baezDuarteGramEntry_symm 8 5]
  exact G5_8_formula

theorem G8_5_interval :
    ((((2514001/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 5) ∧
    (baezDuarteGramEntry 8 5 ≤ (((2516999/14990000) : ℚ) : ℝ)) := by
  rw [G8_5_formula]
  exact vasyuninBEntry_5_8_eval

def interval_8_5 : NamedVasyuninInterval :=
{
  h := 8
  k := 5
  lower := (2514001/14990000)
  upper := (2516999/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_5_interval
}

theorem G8_6_formula : baezDuarteGramEntry 8 6 = vasyuninBEntry 6 8 := by
  rw [baezDuarteGramEntry_symm 8 6]
  exact G6_8_formula

theorem G8_6_interval :
    ((((6315993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 6) ∧
    (baezDuarteGramEntry 8 6 ≤ (((6324007/40070000) : ℚ) : ℝ)) := by
  rw [G8_6_formula]
  exact vasyuninBEntry_6_8_eval

def interval_8_6 : NamedVasyuninInterval :=
{
  h := 8
  k := 6
  lower := (6315993/40070000)
  upper := (6324007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_6_interval
}

theorem G8_7_formula : baezDuarteGramEntry 8 7 = vasyuninBEntry 7 8 := by
  rw [baezDuarteGramEntry_symm 8 7]
  exact G7_8_formula

theorem G8_7_interval :
    ((((27455929/180710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 7) ∧
    (baezDuarteGramEntry 8 7 ≤ (((27492071/180710000) : ℚ) : ℝ)) := by
  rw [G8_7_formula]
  exact vasyuninBEntry_7_8_eval

def interval_8_7 : NamedVasyuninInterval :=
{
  h := 8
  k := 7
  lower := (27455929/180710000)
  upper := (27492071/180710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_7_interval
}

theorem G8_8_formula_eq : baezDuarteGramEntry 8 8 = (1 / (8 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 8 := by norm_num
  rw [baez_duarte_diagonal_scaling 8 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G8_8_log_gamma_interval :
  ((((77955499/495010000) : ℚ) : ℝ) ≤ (1 / (8 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (8 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((78054501/495010000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 8 (by norm_num)
  constructor
  · have : ((((77955499/495010000) : ℚ) : ℝ) ≤ (1 / (8 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (8 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((78054501/495010000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G8_8_interval : ((((77955499/495010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 8) ∧ (baezDuarteGramEntry 8 8 ≤ (((78054501/495010000) : ℚ) : ℝ)) := by
  rw [G8_8_formula_eq]
  exact G8_8_log_gamma_interval

def interval_8_8 : NamedVasyuninInterval :=
{
  h := 8
  k := 8
  lower := (77955499/495010000)
  upper := (78054501/495010000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G8_8_interval
}

theorem G8_9_formula : baezDuarteGramEntry 8 9 = vasyuninBEntry 8 9 := vasyuninBEntry_correct_axiom 8 9

theorem vasyuninBEntry_8_9_eval :
    ((((11758283/87170000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 9) ∧
    (vasyuninBEntry 8 9 ≤ (((11775717/87170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_89_formula_bound
  constructor <;> linarith

theorem G8_9_interval :
    ((((11758283/87170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 9) ∧
    (baezDuarteGramEntry 8 9 ≤ (((11775717/87170000) : ℚ) : ℝ)) := by
  rw [G8_9_formula]
  exact vasyuninBEntry_8_9_eval

def interval_8_9 : NamedVasyuninInterval :=
{
  h := 8
  k := 9
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_9_interval
}

theorem G8_10_formula : baezDuarteGramEntry 8 10 = vasyuninBEntry 8 10 := vasyuninBEntry_correct_axiom 8 10

theorem vasyuninBEntry_8_10_eval :
    ((((12715961/102890000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 10) ∧
    (vasyuninBEntry 8 10 ≤ (((12736539/102890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_10_interval :
    ((((12715961/102890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 10) ∧
    (baezDuarteGramEntry 8 10 ≤ (((12736539/102890000) : ℚ) : ℝ)) := by
  rw [G8_10_formula]
  exact vasyuninBEntry_8_10_eval

def interval_8_10 : NamedVasyuninInterval :=
{
  h := 8
  k := 10
  lower := (12715961/102890000)
  upper := (12736539/102890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_10_interval
}

theorem G9_1_formula : baezDuarteGramEntry 9 1 = vasyuninBEntry 1 9 := by
  rw [baezDuarteGramEntry_symm 9 1]
  exact G1_9_formula

theorem G9_1_interval :
    ((((214204061/859390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 1) ∧
    (baezDuarteGramEntry 9 1 ≤ (((214375939/859390000) : ℚ) : ℝ)) := by
  rw [G9_1_formula]
  exact vasyuninBEntry_1_9_eval

def interval_9_1 : NamedVasyuninInterval :=
{
  h := 9
  k := 1
  lower := (214204061/859390000)
  upper := (214375939/859390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_1_interval
}

theorem G9_2_formula : baezDuarteGramEntry 9 2 = vasyuninBEntry 2 9 := by
  rw [baezDuarteGramEntry_symm 9 2]
  exact G2_9_formula

theorem G9_2_interval :
    ((((135824899/651010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 2) ∧
    (baezDuarteGramEntry 9 2 ≤ (((135955101/651010000) : ℚ) : ℝ)) := by
  rw [G9_2_formula]
  exact vasyuninBEntry_2_9_eval

def interval_9_2 : NamedVasyuninInterval :=
{
  h := 9
  k := 2
  lower := (135824899/651010000)
  upper := (135955101/651010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_2_interval
}

theorem G9_3_formula : baezDuarteGramEntry 9 3 = vasyuninBEntry 3 9 := by
  rw [baezDuarteGramEntry_symm 9 3]
  exact G3_9_formula

theorem G9_3_interval :
    ((((124245143/648570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 3) ∧
    (baezDuarteGramEntry 9 3 ≤ (((124374857/648570000) : ℚ) : ℝ)) := by
  rw [G9_3_formula]
  exact vasyuninBEntry_3_9_eval

def interval_9_3 : NamedVasyuninInterval :=
{
  h := 9
  k := 3
  lower := (124245143/648570000)
  upper := (124374857/648570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_3_interval
}

theorem G9_4_formula : baezDuarteGramEntry 9 4 = vasyuninBEntry 4 9 := by
  rw [baezDuarteGramEntry_symm 9 4]
  exact G4_9_formula

theorem G9_4_interval :
    ((((163044103/958970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 4) ∧
    (baezDuarteGramEntry 9 4 ≤ (((163235897/958970000) : ℚ) : ℝ)) := by
  rw [G9_4_formula]
  exact vasyuninBEntry_4_9_eval

def interval_9_4 : NamedVasyuninInterval :=
{
  h := 9
  k := 4
  lower := (163044103/958970000)
  upper := (163235897/958970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_4_interval
}

theorem G9_5_formula : baezDuarteGramEntry 9 5 = vasyuninBEntry 5 9 := by
  rw [baezDuarteGramEntry_symm 9 5]
  exact G5_9_formula

theorem G9_5_interval :
    ((((17229039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 5) ∧
    (baezDuarteGramEntry 9 5 ≤ (((17250961/109610000) : ℚ) : ℝ)) := by
  rw [G9_5_formula]
  exact vasyuninBEntry_5_9_eval

def interval_9_5 : NamedVasyuninInterval :=
{
  h := 9
  k := 5
  lower := (17229039/109610000)
  upper := (17250961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_5_interval
}

theorem G9_6_formula : baezDuarteGramEntry 9 6 = vasyuninBEntry 6 9 := by
  rw [baezDuarteGramEntry_symm 9 6]
  exact G6_9_formula

theorem G9_6_interval :
    ((((71076627/483730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 6) ∧
    (baezDuarteGramEntry 9 6 ≤ (((71173373/483730000) : ℚ) : ℝ)) := by
  rw [G9_6_formula]
  exact vasyuninBEntry_6_9_eval

def interval_9_6 : NamedVasyuninInterval :=
{
  h := 9
  k := 6
  lower := (71076627/483730000)
  upper := (71173373/483730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_6_interval
}

theorem G9_7_formula : baezDuarteGramEntry 9 7 = vasyuninBEntry 7 9 := by
  rw [baezDuarteGramEntry_symm 9 7]
  exact G7_9_formula

theorem G9_7_interval :
    ((((34032863/246370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 7) ∧
    (baezDuarteGramEntry 9 7 ≤ (((34082137/246370000) : ℚ) : ℝ)) := by
  rw [G9_7_formula]
  exact vasyuninBEntry_7_9_eval

def interval_9_7 : NamedVasyuninInterval :=
{
  h := 9
  k := 7
  lower := (34032863/246370000)
  upper := (34082137/246370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_7_interval
}

theorem G9_8_formula : baezDuarteGramEntry 9 8 = vasyuninBEntry 8 9 := by
  rw [baezDuarteGramEntry_symm 9 8]
  exact G8_9_formula

theorem G9_8_interval :
    ((((11758283/87170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 8) ∧
    (baezDuarteGramEntry 9 8 ≤ (((11775717/87170000) : ℚ) : ℝ)) := by
  rw [G9_8_formula]
  exact vasyuninBEntry_8_9_eval

def interval_9_8 : NamedVasyuninInterval :=
{
  h := 9
  k := 8
  lower := (11758283/87170000)
  upper := (11775717/87170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_8_interval
}

theorem G9_9_formula_eq : baezDuarteGramEntry 9 9 = (1 / (9 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 9 := by norm_num
  rw [baez_duarte_diagonal_scaling 9 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G9_9_log_gamma_interval :
  ((((12571019/89810000) : ℚ) : ℝ) ≤ (1 / (9 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (9 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((12588981/89810000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 9 (by norm_num)
  constructor
  · have : ((((12571019/89810000) : ℚ) : ℝ) ≤ (1 / (9 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (9 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((12588981/89810000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G9_9_interval : ((((12571019/89810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 9) ∧ (baezDuarteGramEntry 9 9 ≤ (((12588981/89810000) : ℚ) : ℝ)) := by
  rw [G9_9_formula_eq]
  exact G9_9_log_gamma_interval

def interval_9_9 : NamedVasyuninInterval :=
{
  h := 9
  k := 9
  lower := (12571019/89810000)
  upper := (12588981/89810000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G9_9_interval
}

theorem G9_10_formula : baezDuarteGramEntry 9 10 = vasyuninBEntry 9 10 := vasyuninBEntry_correct_axiom 9 10

theorem vasyuninBEntry_9_10_eval :
    ((((116434047/959530000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 10) ∧
    (vasyuninBEntry 9 10 ≤ (((116625953/959530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_910_formula_bound
  constructor <;> linarith

theorem G9_10_interval :
    ((((116434047/959530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 10) ∧
    (baezDuarteGramEntry 9 10 ≤ (((116625953/959530000) : ℚ) : ℝ)) := by
  rw [G9_10_formula]
  exact vasyuninBEntry_9_10_eval

def interval_9_10 : NamedVasyuninInterval :=
{
  h := 9
  k := 10
  lower := (116434047/959530000)
  upper := (116625953/959530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_10_interval
}

theorem G10_1_formula : baezDuarteGramEntry 10 1 = vasyuninBEntry 1 10 := by
  rw [baezDuarteGramEntry_symm 10 1]
  exact G1_10_formula

theorem G10_1_interval :
    ((((16135967/70330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 1) ∧
    (baezDuarteGramEntry 10 1 ≤ (((16150033/70330000) : ℚ) : ℝ)) := by
  rw [G10_1_formula]
  exact vasyuninBEntry_1_10_eval

def interval_10_1 : NamedVasyuninInterval :=
{
  h := 10
  k := 1
  lower := (16135967/70330000)
  upper := (16150033/70330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_1_interval
}

theorem G10_2_formula : baezDuarteGramEntry 10 2 = vasyuninBEntry 2 10 := by
  rw [baezDuarteGramEntry_symm 10 2]
  exact G2_10_formula

theorem G10_2_interval :
    ((((64257239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 2) ∧
    (baezDuarteGramEntry 10 2 ≤ (((64322761/327610000) : ℚ) : ℝ)) := by
  rw [G10_2_formula]
  exact vasyuninBEntry_2_10_eval

def interval_10_2 : NamedVasyuninInterval :=
{
  h := 10
  k := 2
  lower := (64257239/327610000)
  upper := (64322761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_2_interval
}

theorem G10_3_formula : baezDuarteGramEntry 10 3 = vasyuninBEntry 3 10 := by
  rw [baezDuarteGramEntry_symm 10 3]
  exact G3_10_formula

theorem G10_3_interval :
    ((((64452631/373690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 3) ∧
    (baezDuarteGramEntry 10 3 ≤ (((64527369/373690000) : ℚ) : ℝ)) := by
  rw [G10_3_formula]
  exact vasyuninBEntry_3_10_eval

def interval_10_3 : NamedVasyuninInterval :=
{
  h := 10
  k := 3
  lower := (64452631/373690000)
  upper := (64527369/373690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_3_interval
}

theorem G10_4_formula : baezDuarteGramEntry 10 4 = vasyuninBEntry 4 10 := by
  rw [baezDuarteGramEntry_symm 10 4]
  exact G4_10_formula

theorem G10_4_interval :
    ((((18243461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 4) ∧
    (baezDuarteGramEntry 10 4 ≤ (((18266539/115390000) : ℚ) : ℝ)) := by
  rw [G10_4_formula]
  exact vasyuninBEntry_4_10_eval

def interval_10_4 : NamedVasyuninInterval :=
{
  h := 10
  k := 4
  lower := (18243461/115390000)
  upper := (18266539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_4_interval
}

theorem G10_5_formula : baezDuarteGramEntry 10 5 = vasyuninBEntry 5 10 := by
  rw [baezDuarteGramEntry_symm 10 5]
  exact G5_10_formula

theorem G10_5_interval :
    ((((50922007/329930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 5) ∧
    (baezDuarteGramEntry 10 5 ≤ (((50987993/329930000) : ℚ) : ℝ)) := by
  rw [G10_5_formula]
  exact vasyuninBEntry_5_10_eval

def interval_10_5 : NamedVasyuninInterval :=
{
  h := 10
  k := 5
  lower := (50922007/329930000)
  upper := (50987993/329930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_5_interval
}

theorem G10_6_formula : baezDuarteGramEntry 10 6 = vasyuninBEntry 6 10 := by
  rw [baezDuarteGramEntry_symm 10 6]
  exact G6_10_formula

theorem G10_6_interval :
    ((((40310507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 10 6) ∧
    (baezDuarteGramEntry 10 6 ≤ (((40369493/294930000) : ℚ) : ℝ)) := by
  rw [G10_6_formula]
  exact vasyuninBEntry_6_10_eval

def interval_10_6 : NamedVasyuninInterval :=
{
  h := 10
  k := 6
  lower := (40310507/294930000)
  upper := (40369493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G10_6_interval
}

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

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN10
