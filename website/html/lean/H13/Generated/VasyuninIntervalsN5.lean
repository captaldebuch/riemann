import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5
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

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN5
