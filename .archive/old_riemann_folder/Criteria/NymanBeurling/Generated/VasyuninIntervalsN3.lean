import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G1_1_formula_axiom : baezDuarteGramEntry 1 1 = (1 / (1 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
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

theorem G1_1_interval_axiom : ((((6303/5000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 1) ∧ (baezDuarteGramEntry 1 1 ≤ (((12607/10000) : ℚ) : ℝ)) := by
  rw [G1_1_formula_axiom]
  exact G1_1_log_gamma_interval

def interval_1_1 : NamedVasyuninInterval :=
{
  h := 1
  k := 1
  lower := (6303/5000)
  upper := (12607/10000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G1_1_interval_axiom
}

theorem G1_2_formula : baezDuarteGramEntry 1 2 = vasyuninBEntry 1 2 := vasyuninBEntry_correct_axiom 1 2 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_2_eval :
    ((((3861/5000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 2) ∧
    (vasyuninBEntry 1 2 ≤ (((7723/10000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_12_formula_bound
  constructor <;> linarith

theorem G1_2_interval_axiom :
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
  interval_proof := G1_2_interval_axiom
}

theorem G1_3_formula : baezDuarteGramEntry 1 3 = vasyuninBEntry 1 3 := vasyuninBEntry_correct_axiom 1 3 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_3_eval :
    ((((23/40) : ℚ) : ℝ) ≤ vasyuninBEntry 1 3) ∧
    (vasyuninBEntry 1 3 ≤ (((5751/10000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_13_formula_bound
  constructor <;> linarith

theorem G1_3_interval_axiom :
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
  interval_proof := G1_3_interval_axiom
}

theorem G2_1_formula : baezDuarteGramEntry 2 1 = vasyuninBEntry 1 2 := by
  rw [baezDuarteGramEntry_symm 2 1]
  exact G1_2_formula

theorem G2_1_interval_axiom :
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
  interval_proof := G2_1_interval_axiom
}

theorem G2_2_formula_axiom : baezDuarteGramEntry 2 2 = (1 / (2 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
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

theorem G2_2_interval_axiom : ((((6303/10000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 2) ∧ (baezDuarteGramEntry 2 2 ≤ (((394/625) : ℚ) : ℝ)) := by
  rw [G2_2_formula_axiom]
  exact G2_2_log_gamma_interval

def interval_2_2 : NamedVasyuninInterval :=
{
  h := 2
  k := 2
  lower := (6303/10000)
  upper := (394/625)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G2_2_interval_axiom
}

theorem G2_3_formula : baezDuarteGramEntry 2 3 = vasyuninBEntry 2 3 := vasyuninBEntry_correct_axiom 2 3 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_3_eval :
    ((((4411/10000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 3) ∧
    (vasyuninBEntry 2 3 ≤ (((1103/2500) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_23_formula_bound
  constructor <;> linarith

theorem G2_3_interval_axiom :
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
  interval_proof := G2_3_interval_axiom
}

theorem G3_1_formula : baezDuarteGramEntry 3 1 = vasyuninBEntry 1 3 := by
  rw [baezDuarteGramEntry_symm 3 1]
  exact G1_3_formula

theorem G3_1_interval_axiom :
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
  interval_proof := G3_1_interval_axiom
}

theorem G3_2_formula : baezDuarteGramEntry 3 2 = vasyuninBEntry 2 3 := by
  rw [baezDuarteGramEntry_symm 3 2]
  exact G2_3_formula

theorem G3_2_interval_axiom :
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
  interval_proof := G3_2_interval_axiom
}

theorem G3_3_formula_axiom : baezDuarteGramEntry 3 3 = (1 / (3 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
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

theorem G3_3_interval_axiom : ((((2101/5000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 3) ∧ (baezDuarteGramEntry 3 3 ≤ (((4203/10000) : ℚ) : ℝ)) := by
  rw [G3_3_formula_axiom]
  exact G3_3_log_gamma_interval

def interval_3_3 : NamedVasyuninInterval :=
{
  h := 3
  k := 3
  lower := (2101/5000)
  upper := (4203/10000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G3_3_interval_axiom
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN3
