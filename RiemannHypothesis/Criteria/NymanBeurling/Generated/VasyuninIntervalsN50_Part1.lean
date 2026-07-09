import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
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

theorem G1_2_formula : baezDuarteGramEntry 1 2 = vasyuninBEntry 1 2 := vasyuninBEntry_correct_axiom 1 2 (by norm_num) (by norm_num)

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

theorem G1_3_formula : baezDuarteGramEntry 1 3 = vasyuninBEntry 1 3 := vasyuninBEntry_correct_axiom 1 3 (by norm_num) (by norm_num)

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

theorem G1_4_formula : baezDuarteGramEntry 1 4 = vasyuninBEntry 1 4 := vasyuninBEntry_correct_axiom 1 4 (by norm_num) (by norm_num)

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

theorem G1_5_formula : baezDuarteGramEntry 1 5 = vasyuninBEntry 1 5 := vasyuninBEntry_correct_axiom 1 5 (by norm_num) (by norm_num)

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

theorem G1_6_formula : baezDuarteGramEntry 1 6 = vasyuninBEntry 1 6 := vasyuninBEntry_correct_axiom 1 6 (by norm_num) (by norm_num)

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

theorem G1_7_formula : baezDuarteGramEntry 1 7 = vasyuninBEntry 1 7 := vasyuninBEntry_correct_axiom 1 7 (by norm_num) (by norm_num)

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

theorem G1_8_formula : baezDuarteGramEntry 1 8 = vasyuninBEntry 1 8 := vasyuninBEntry_correct_axiom 1 8 (by norm_num) (by norm_num)

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

theorem G1_9_formula : baezDuarteGramEntry 1 9 = vasyuninBEntry 1 9 := vasyuninBEntry_correct_axiom 1 9 (by norm_num) (by norm_num)

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

theorem G1_10_formula : baezDuarteGramEntry 1 10 = vasyuninBEntry 1 10 := vasyuninBEntry_correct_axiom 1 10 (by norm_num) (by norm_num)

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

theorem G1_11_formula : baezDuarteGramEntry 1 11 = vasyuninBEntry 1 11 := vasyuninBEntry_correct_axiom 1 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_11_eval :
    ((((12924551/60740000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 11) ∧
    (vasyuninBEntry 1 11 ≤ (((12936699/60740000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_111_formula_bound
  constructor <;> linarith

theorem G1_11_interval :
    ((((12924551/60740000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 11) ∧
    (baezDuarteGramEntry 1 11 ≤ (((12936699/60740000) : ℚ) : ℝ)) := by
  rw [G1_11_formula]
  exact vasyuninBEntry_1_11_eval

def interval_1_11 : NamedVasyuninInterval :=
{
  h := 1
  k := 11
  lower := (12924551/60740000)
  upper := (12936699/60740000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_11_interval
}

theorem G1_12_formula : baezDuarteGramEntry 1 12 = vasyuninBEntry 1 12 := vasyuninBEntry_correct_axiom 1 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_12_eval :
    ((((47665997/240030000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 12) ∧
    (vasyuninBEntry 1 12 ≤ (((47714003/240030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_112_formula_bound
  constructor <;> linarith

theorem G1_12_interval :
    ((((47665997/240030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 12) ∧
    (baezDuarteGramEntry 1 12 ≤ (((47714003/240030000) : ℚ) : ℝ)) := by
  rw [G1_12_formula]
  exact vasyuninBEntry_1_12_eval

def interval_1_12 : NamedVasyuninInterval :=
{
  h := 1
  k := 12
  lower := (47665997/240030000)
  upper := (47714003/240030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_12_interval
}

theorem G1_13_formula : baezDuarteGramEntry 1 13 = vasyuninBEntry 1 13 := vasyuninBEntry_correct_axiom 1 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_13_eval :
    ((((53581241/287590000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 13) ∧
    (vasyuninBEntry 1 13 ≤ (((53638759/287590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_113_formula_bound
  constructor <;> linarith

theorem G1_13_interval :
    ((((53581241/287590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 13) ∧
    (baezDuarteGramEntry 1 13 ≤ (((53638759/287590000) : ℚ) : ℝ)) := by
  rw [G1_13_formula]
  exact vasyuninBEntry_1_13_eval

def interval_1_13 : NamedVasyuninInterval :=
{
  h := 1
  k := 13
  lower := (53581241/287590000)
  upper := (53638759/287590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_13_interval
}

theorem G1_14_formula : baezDuarteGramEntry 1 14 = vasyuninBEntry 1 14 := vasyuninBEntry_correct_axiom 1 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_14_eval :
    ((((150274417/855830000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 14) ∧
    (vasyuninBEntry 1 14 ≤ (((150445583/855830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_114_formula_bound
  constructor <;> linarith

theorem G1_14_interval :
    ((((150274417/855830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 14) ∧
    (baezDuarteGramEntry 1 14 ≤ (((150445583/855830000) : ℚ) : ℝ)) := by
  rw [G1_14_formula]
  exact vasyuninBEntry_1_14_eval

def interval_1_14 : NamedVasyuninInterval :=
{
  h := 1
  k := 14
  lower := (150274417/855830000)
  upper := (150445583/855830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_14_interval
}

theorem G1_15_formula : baezDuarteGramEntry 1 15 = vasyuninBEntry 1 15 := vasyuninBEntry_correct_axiom 1 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_15_eval :
    ((((161452817/971830000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 15) ∧
    (vasyuninBEntry 1 15 ≤ (((161647183/971830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_115_formula_bound
  constructor <;> linarith

theorem G1_15_interval :
    ((((161452817/971830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 15) ∧
    (baezDuarteGramEntry 1 15 ≤ (((161647183/971830000) : ℚ) : ℝ)) := by
  rw [G1_15_formula]
  exact vasyuninBEntry_1_15_eval

def interval_1_15 : NamedVasyuninInterval :=
{
  h := 1
  k := 15
  lower := (161452817/971830000)
  upper := (161647183/971830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_15_interval
}

theorem G1_16_formula : baezDuarteGramEntry 1 16 = vasyuninBEntry 1 16 := vasyuninBEntry_correct_axiom 1 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_16_eval :
    ((((149864983/950170000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 16) ∧
    (vasyuninBEntry 1 16 ≤ (((150055017/950170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_116_formula_bound
  constructor <;> linarith

theorem G1_16_interval :
    ((((149864983/950170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 16) ∧
    (baezDuarteGramEntry 1 16 ≤ (((150055017/950170000) : ℚ) : ℝ)) := by
  rw [G1_16_formula]
  exact vasyuninBEntry_1_16_eval

def interval_1_16 : NamedVasyuninInterval :=
{
  h := 1
  k := 16
  lower := (149864983/950170000)
  upper := (150055017/950170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_16_interval
}

theorem G1_17_formula : baezDuarteGramEntry 1 17 = vasyuninBEntry 1 17 := vasyuninBEntry_correct_axiom 1 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_17_eval :
    ((((149910189/998110000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 17) ∧
    (vasyuninBEntry 1 17 ≤ (((150109811/998110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_117_formula_bound
  constructor <;> linarith

theorem G1_17_interval :
    ((((149910189/998110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 17) ∧
    (baezDuarteGramEntry 1 17 ≤ (((150109811/998110000) : ℚ) : ℝ)) := by
  rw [G1_17_formula]
  exact vasyuninBEntry_1_17_eval

def interval_1_17 : NamedVasyuninInterval :=
{
  h := 1
  k := 17
  lower := (149910189/998110000)
  upper := (150109811/998110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_17_interval
}

theorem G1_18_formula : baezDuarteGramEntry 1 18 = vasyuninBEntry 1 18 := vasyuninBEntry_correct_axiom 1 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_18_eval :
    ((((65389403/455970000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 18) ∧
    (vasyuninBEntry 1 18 ≤ (((65480597/455970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_118_formula_bound
  constructor <;> linarith

theorem G1_18_interval :
    ((((65389403/455970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 18) ∧
    (baezDuarteGramEntry 1 18 ≤ (((65480597/455970000) : ℚ) : ℝ)) := by
  rw [G1_18_formula]
  exact vasyuninBEntry_1_18_eval

def interval_1_18 : NamedVasyuninInterval :=
{
  h := 1
  k := 18
  lower := (65389403/455970000)
  upper := (65480597/455970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_18_interval
}

theorem G1_19_formula : baezDuarteGramEntry 1 19 = vasyuninBEntry 1 19 := vasyuninBEntry_correct_axiom 1 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_19_eval :
    ((((2263351/16490000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 19) ∧
    (vasyuninBEntry 1 19 ≤ (((2266649/16490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_119_formula_bound
  constructor <;> linarith

theorem G1_19_interval :
    ((((2263351/16490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 19) ∧
    (baezDuarteGramEntry 1 19 ≤ (((2266649/16490000) : ℚ) : ℝ)) := by
  rw [G1_19_formula]
  exact vasyuninBEntry_1_19_eval

def interval_1_19 : NamedVasyuninInterval :=
{
  h := 1
  k := 19
  lower := (2263351/16490000)
  upper := (2266649/16490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_19_interval
}

theorem G1_20_formula : baezDuarteGramEntry 1 20 = vasyuninBEntry 1 20 := vasyuninBEntry_correct_axiom 1 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_20_eval :
    ((((44721031/339690000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 20) ∧
    (vasyuninBEntry 1 20 ≤ (((44788969/339690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_120_formula_bound
  constructor <;> linarith

theorem G1_20_interval :
    ((((44721031/339690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 20) ∧
    (baezDuarteGramEntry 1 20 ≤ (((44788969/339690000) : ℚ) : ℝ)) := by
  rw [G1_20_formula]
  exact vasyuninBEntry_1_20_eval

def interval_1_20 : NamedVasyuninInterval :=
{
  h := 1
  k := 20
  lower := (44721031/339690000)
  upper := (44788969/339690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_20_interval
}

theorem G1_21_formula : baezDuarteGramEntry 1 21 = vasyuninBEntry 1 21 := vasyuninBEntry_correct_axiom 1 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_21_eval :
    ((((97053293/767070000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 21) ∧
    (vasyuninBEntry 1 21 ≤ (((97206707/767070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_121_formula_bound
  constructor <;> linarith

theorem G1_21_interval :
    ((((97053293/767070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 21) ∧
    (baezDuarteGramEntry 1 21 ≤ (((97206707/767070000) : ℚ) : ℝ)) := by
  rw [G1_21_formula]
  exact vasyuninBEntry_1_21_eval

def interval_1_21 : NamedVasyuninInterval :=
{
  h := 1
  k := 21
  lower := (97053293/767070000)
  upper := (97206707/767070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_21_interval
}

theorem G1_22_formula : baezDuarteGramEntry 1 22 = vasyuninBEntry 1 22 := vasyuninBEntry_correct_axiom 1 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_22_eval :
    ((((7348967/60330000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 22) ∧
    (vasyuninBEntry 1 22 ≤ (((7361033/60330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_122_formula_bound
  constructor <;> linarith

theorem G1_22_interval :
    ((((7348967/60330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 22) ∧
    (baezDuarteGramEntry 1 22 ≤ (((7361033/60330000) : ℚ) : ℝ)) := by
  rw [G1_22_formula]
  exact vasyuninBEntry_1_22_eval

def interval_1_22 : NamedVasyuninInterval :=
{
  h := 1
  k := 22
  lower := (7348967/60330000)
  upper := (7361033/60330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_22_interval
}

theorem G1_23_formula : baezDuarteGramEntry 1 23 = vasyuninBEntry 1 23 := vasyuninBEntry_correct_axiom 1 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_23_eval :
    ((((57700879/491210000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 23) ∧
    (vasyuninBEntry 1 23 ≤ (((57799121/491210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_123_formula_bound
  constructor <;> linarith

theorem G1_23_interval :
    ((((57700879/491210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 23) ∧
    (baezDuarteGramEntry 1 23 ≤ (((57799121/491210000) : ℚ) : ℝ)) := by
  rw [G1_23_formula]
  exact vasyuninBEntry_1_23_eval

def interval_1_23 : NamedVasyuninInterval :=
{
  h := 1
  k := 23
  lower := (57700879/491210000)
  upper := (57799121/491210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_23_interval
}

theorem G1_24_formula : baezDuarteGramEntry 1 24 = vasyuninBEntry 1 24 := vasyuninBEntry_correct_axiom 1 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_24_eval :
    ((((71586897/631030000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 24) ∧
    (vasyuninBEntry 1 24 ≤ (((71713103/631030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_124_formula_bound
  constructor <;> linarith

theorem G1_24_interval :
    ((((71586897/631030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 24) ∧
    (baezDuarteGramEntry 1 24 ≤ (((71713103/631030000) : ℚ) : ℝ)) := by
  rw [G1_24_formula]
  exact vasyuninBEntry_1_24_eval

def interval_1_24 : NamedVasyuninInterval :=
{
  h := 1
  k := 24
  lower := (71586897/631030000)
  upper := (71713103/631030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_24_interval
}

theorem G1_25_formula : baezDuarteGramEntry 1 25 = vasyuninBEntry 1 25 := vasyuninBEntry_correct_axiom 1 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_25_eval :
    ((((21774153/198470000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 25) ∧
    (vasyuninBEntry 1 25 ≤ (((21813847/198470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_125_formula_bound
  constructor <;> linarith

theorem G1_25_interval :
    ((((21774153/198470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 25) ∧
    (baezDuarteGramEntry 1 25 ≤ (((21813847/198470000) : ℚ) : ℝ)) := by
  rw [G1_25_formula]
  exact vasyuninBEntry_1_25_eval

def interval_1_25 : NamedVasyuninInterval :=
{
  h := 1
  k := 25
  lower := (21774153/198470000)
  upper := (21813847/198470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_25_interval
}

theorem G1_26_formula : baezDuarteGramEntry 1 26 = vasyuninBEntry 1 26 := vasyuninBEntry_correct_axiom 1 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_26_eval :
    ((((32829097/309030000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 26) ∧
    (vasyuninBEntry 1 26 ≤ (((32890903/309030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_126_formula_bound
  constructor <;> linarith

theorem G1_26_interval :
    ((((32829097/309030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 26) ∧
    (baezDuarteGramEntry 1 26 ≤ (((32890903/309030000) : ℚ) : ℝ)) := by
  rw [G1_26_formula]
  exact vasyuninBEntry_1_26_eval

def interval_1_26 : NamedVasyuninInterval :=
{
  h := 1
  k := 26
  lower := (32829097/309030000)
  upper := (32890903/309030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_26_interval
}

theorem G1_27_formula : baezDuarteGramEntry 1 27 = vasyuninBEntry 1 27 := vasyuninBEntry_correct_axiom 1 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_27_eval :
    ((((95806971/930290000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 27) ∧
    (vasyuninBEntry 1 27 ≤ (((95993029/930290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_127_formula_bound
  constructor <;> linarith

theorem G1_27_interval :
    ((((95806971/930290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 27) ∧
    (baezDuarteGramEntry 1 27 ≤ (((95993029/930290000) : ℚ) : ℝ)) := by
  rw [G1_27_formula]
  exact vasyuninBEntry_1_27_eval

def interval_1_27 : NamedVasyuninInterval :=
{
  h := 1
  k := 27
  lower := (95806971/930290000)
  upper := (95993029/930290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_27_interval
}

theorem G1_28_formula : baezDuarteGramEntry 1 28 = vasyuninBEntry 1 28 := vasyuninBEntry_correct_axiom 1 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_28_eval :
    ((((14749243/147570000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 28) ∧
    (vasyuninBEntry 1 28 ≤ (((14778757/147570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_128_formula_bound
  constructor <;> linarith

theorem G1_28_interval :
    ((((14749243/147570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 28) ∧
    (baezDuarteGramEntry 1 28 ≤ (((14778757/147570000) : ℚ) : ℝ)) := by
  rw [G1_28_formula]
  exact vasyuninBEntry_1_28_eval

def interval_1_28 : NamedVasyuninInterval :=
{
  h := 1
  k := 28
  lower := (14749243/147570000)
  upper := (14778757/147570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_28_interval
}

theorem G1_29_formula : baezDuarteGramEntry 1 29 = vasyuninBEntry 1 29 := vasyuninBEntry_correct_axiom 1 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_29_eval :
    ((((81985563/844370000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 29) ∧
    (vasyuninBEntry 1 29 ≤ (((82154437/844370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_129_formula_bound
  constructor <;> linarith

theorem G1_29_interval :
    ((((81985563/844370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 29) ∧
    (baezDuarteGramEntry 1 29 ≤ (((82154437/844370000) : ℚ) : ℝ)) := by
  rw [G1_29_formula]
  exact vasyuninBEntry_1_29_eval

def interval_1_29 : NamedVasyuninInterval :=
{
  h := 1
  k := 29
  lower := (81985563/844370000)
  upper := (82154437/844370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_29_interval
}

theorem G1_30_formula : baezDuarteGramEntry 1 30 = vasyuninBEntry 1 30 := vasyuninBEntry_correct_axiom 1 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_30_eval :
    ((((42375119/448810000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 30) ∧
    (vasyuninBEntry 1 30 ≤ (((42464881/448810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_130_formula_bound
  constructor <;> linarith

theorem G1_30_interval :
    ((((42375119/448810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 30) ∧
    (baezDuarteGramEntry 1 30 ≤ (((42464881/448810000) : ℚ) : ℝ)) := by
  rw [G1_30_formula]
  exact vasyuninBEntry_1_30_eval

def interval_1_30 : NamedVasyuninInterval :=
{
  h := 1
  k := 30
  lower := (42375119/448810000)
  upper := (42464881/448810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_30_interval
}

theorem G1_31_formula : baezDuarteGramEntry 1 31 = vasyuninBEntry 1 31 := vasyuninBEntry_correct_axiom 1 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_31_eval :
    ((((23764139/258610000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 31) ∧
    (vasyuninBEntry 1 31 ≤ (((23815861/258610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_131_formula_bound
  constructor <;> linarith

theorem G1_31_interval :
    ((((23764139/258610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 31) ∧
    (baezDuarteGramEntry 1 31 ≤ (((23815861/258610000) : ℚ) : ℝ)) := by
  rw [G1_31_formula]
  exact vasyuninBEntry_1_31_eval

def interval_1_31 : NamedVasyuninInterval :=
{
  h := 1
  k := 31
  lower := (23764139/258610000)
  upper := (23815861/258610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_31_interval
}

theorem G1_32_formula : baezDuarteGramEntry 1 32 = vasyuninBEntry 1 32 := vasyuninBEntry_correct_axiom 1 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_32_eval :
    ((((8855107/98930000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 32) ∧
    (vasyuninBEntry 1 32 ≤ (((8874893/98930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_132_formula_bound
  constructor <;> linarith

theorem G1_32_interval :
    ((((8855107/98930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 32) ∧
    (baezDuarteGramEntry 1 32 ≤ (((8874893/98930000) : ℚ) : ℝ)) := by
  rw [G1_32_formula]
  exact vasyuninBEntry_1_32_eval

def interval_1_32 : NamedVasyuninInterval :=
{
  h := 1
  k := 32
  lower := (8855107/98930000)
  upper := (8874893/98930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_32_interval
}

theorem G1_33_formula : baezDuarteGramEntry 1 33 = vasyuninBEntry 1 33 := vasyuninBEntry_correct_axiom 1 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_33_eval :
    ((((61299747/702530000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 33) ∧
    (vasyuninBEntry 1 33 ≤ (((61440253/702530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_133_formula_bound
  constructor <;> linarith

theorem G1_33_interval :
    ((((61299747/702530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 33) ∧
    (baezDuarteGramEntry 1 33 ≤ (((61440253/702530000) : ℚ) : ℝ)) := by
  rw [G1_33_formula]
  exact vasyuninBEntry_1_33_eval

def interval_1_33 : NamedVasyuninInterval :=
{
  h := 1
  k := 33
  lower := (61299747/702530000)
  upper := (61440253/702530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_33_interval
}

theorem G1_34_formula : baezDuarteGramEntry 1 34 = vasyuninBEntry 1 34 := vasyuninBEntry_correct_axiom 1 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_34_eval :
    ((((12988741/152590000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 34) ∧
    (vasyuninBEntry 1 34 ≤ (((13019259/152590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_134_formula_bound
  constructor <;> linarith

theorem G1_34_interval :
    ((((12988741/152590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 34) ∧
    (baezDuarteGramEntry 1 34 ≤ (((13019259/152590000) : ℚ) : ℝ)) := by
  rw [G1_34_formula]
  exact vasyuninBEntry_1_34_eval

def interval_1_34 : NamedVasyuninInterval :=
{
  h := 1
  k := 34
  lower := (12988741/152590000)
  upper := (13019259/152590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_34_interval
}

theorem G1_35_formula : baezDuarteGramEntry 1 35 = vasyuninBEntry 1 35 := vasyuninBEntry_correct_axiom 1 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_35_eval :
    ((((7660781/92190000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 35) ∧
    (vasyuninBEntry 1 35 ≤ (((7679219/92190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_135_formula_bound
  constructor <;> linarith

theorem G1_35_interval :
    ((((7660781/92190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 35) ∧
    (baezDuarteGramEntry 1 35 ≤ (((7679219/92190000) : ℚ) : ℝ)) := by
  rw [G1_35_formula]
  exact vasyuninBEntry_1_35_eval

def interval_1_35 : NamedVasyuninInterval :=
{
  h := 1
  k := 35
  lower := (7660781/92190000)
  upper := (7679219/92190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_35_interval
}

theorem G1_36_formula : baezDuarteGramEntry 1 36 = vasyuninBEntry 1 36 := vasyuninBEntry_correct_axiom 1 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_36_eval :
    ((((18107693/223070000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 36) ∧
    (vasyuninBEntry 1 36 ≤ (((18152307/223070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_136_formula_bound
  constructor <;> linarith

theorem G1_36_interval :
    ((((18107693/223070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 36) ∧
    (baezDuarteGramEntry 1 36 ≤ (((18152307/223070000) : ℚ) : ℝ)) := by
  rw [G1_36_formula]
  exact vasyuninBEntry_1_36_eval

def interval_1_36 : NamedVasyuninInterval :=
{
  h := 1
  k := 36
  lower := (18107693/223070000)
  upper := (18152307/223070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_36_interval
}

theorem G1_37_formula : baezDuarteGramEntry 1 37 = vasyuninBEntry 1 37 := vasyuninBEntry_correct_axiom 1 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_37_eval :
    ((((2290713/28870000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 37) ∧
    (vasyuninBEntry 1 37 ≤ (((2296487/28870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_137_formula_bound
  constructor <;> linarith

theorem G1_37_interval :
    ((((2290713/28870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 37) ∧
    (baezDuarteGramEntry 1 37 ≤ (((2296487/28870000) : ℚ) : ℝ)) := by
  rw [G1_37_formula]
  exact vasyuninBEntry_1_37_eval

def interval_1_37 : NamedVasyuninInterval :=
{
  h := 1
  k := 37
  lower := (2290713/28870000)
  upper := (2296487/28870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_37_interval
}

theorem G1_38_formula : baezDuarteGramEntry 1 38 = vasyuninBEntry 1 38 := vasyuninBEntry_correct_axiom 1 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_38_eval :
    ((((24708161/318390000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 38) ∧
    (vasyuninBEntry 1 38 ≤ (((24771839/318390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_138_formula_bound
  constructor <;> linarith

theorem G1_38_interval :
    ((((24708161/318390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 38) ∧
    (baezDuarteGramEntry 1 38 ≤ (((24771839/318390000) : ℚ) : ℝ)) := by
  rw [G1_38_formula]
  exact vasyuninBEntry_1_38_eval

def interval_1_38 : NamedVasyuninInterval :=
{
  h := 1
  k := 38
  lower := (24708161/318390000)
  upper := (24771839/318390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_38_interval
}

theorem G1_39_formula : baezDuarteGramEntry 1 39 = vasyuninBEntry 1 39 := vasyuninBEntry_correct_axiom 1 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_39_eval :
    ((((26080657/343430000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 39) ∧
    (vasyuninBEntry 1 39 ≤ (((26149343/343430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_139_formula_bound
  constructor <;> linarith

theorem G1_39_interval :
    ((((26080657/343430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 39) ∧
    (baezDuarteGramEntry 1 39 ≤ (((26149343/343430000) : ℚ) : ℝ)) := by
  rw [G1_39_formula]
  exact vasyuninBEntry_1_39_eval

def interval_1_39 : NamedVasyuninInterval :=
{
  h := 1
  k := 39
  lower := (26080657/343430000)
  upper := (26149343/343430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_39_interval
}

theorem G1_40_formula : baezDuarteGramEntry 1 40 = vasyuninBEntry 1 40 := vasyuninBEntry_correct_axiom 1 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_40_eval :
    ((((7366343/99070000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 40) ∧
    (vasyuninBEntry 1 40 ≤ (((7386157/99070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_140_formula_bound
  constructor <;> linarith

theorem G1_40_interval :
    ((((7366343/99070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 40) ∧
    (baezDuarteGramEntry 1 40 ≤ (((7386157/99070000) : ℚ) : ℝ)) := by
  rw [G1_40_formula]
  exact vasyuninBEntry_1_40_eval

def interval_1_40 : NamedVasyuninInterval :=
{
  h := 1
  k := 40
  lower := (7366343/99070000)
  upper := (7386157/99070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_40_interval
}

theorem G1_41_formula : baezDuarteGramEntry 1 41 = vasyuninBEntry 1 41 := vasyuninBEntry_correct_axiom 1 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_41_eval :
    ((((56422537/774630000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 41) ∧
    (vasyuninBEntry 1 41 ≤ (((56577463/774630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_141_formula_bound
  constructor <;> linarith

theorem G1_41_interval :
    ((((56422537/774630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 41) ∧
    (baezDuarteGramEntry 1 41 ≤ (((56577463/774630000) : ℚ) : ℝ)) := by
  rw [G1_41_formula]
  exact vasyuninBEntry_1_41_eval

def interval_1_41 : NamedVasyuninInterval :=
{
  h := 1
  k := 41
  lower := (56422537/774630000)
  upper := (56577463/774630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_41_interval
}

theorem G1_42_formula : baezDuarteGramEntry 1 42 = vasyuninBEntry 1 42 := vasyuninBEntry_correct_axiom 1 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_42_eval :
    ((((1234271/17290000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 42) ∧
    (vasyuninBEntry 1 42 ≤ (((1237729/17290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_142_formula_bound
  constructor <;> linarith

theorem G1_42_interval :
    ((((1234271/17290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 42) ∧
    (baezDuarteGramEntry 1 42 ≤ (((1237729/17290000) : ℚ) : ℝ)) := by
  rw [G1_42_formula]
  exact vasyuninBEntry_1_42_eval

def interval_1_42 : NamedVasyuninInterval :=
{
  h := 1
  k := 42
  lower := (1234271/17290000)
  upper := (1237729/17290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_42_interval
}

theorem G1_43_formula : baezDuarteGramEntry 1 43 = vasyuninBEntry 1 43 := vasyuninBEntry_correct_axiom 1 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_43_eval :
    ((((60583447/865530000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 43) ∧
    (vasyuninBEntry 1 43 ≤ (((60756553/865530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_143_formula_bound
  constructor <;> linarith

theorem G1_43_interval :
    ((((60583447/865530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 43) ∧
    (baezDuarteGramEntry 1 43 ≤ (((60756553/865530000) : ℚ) : ℝ)) := by
  rw [G1_43_formula]
  exact vasyuninBEntry_1_43_eval

def interval_1_43 : NamedVasyuninInterval :=
{
  h := 1
  k := 43
  lower := (60583447/865530000)
  upper := (60756553/865530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_43_interval
}

theorem G1_44_formula : baezDuarteGramEntry 1 44 = vasyuninBEntry 1 44 := vasyuninBEntry_correct_axiom 1 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_44_eval :
    ((((17097599/249010000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 44) ∧
    (vasyuninBEntry 1 44 ≤ (((17147401/249010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_144_formula_bound
  constructor <;> linarith

theorem G1_44_interval :
    ((((17097599/249010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 44) ∧
    (baezDuarteGramEntry 1 44 ≤ (((17147401/249010000) : ℚ) : ℝ)) := by
  rw [G1_44_formula]
  exact vasyuninBEntry_1_44_eval

def interval_1_44 : NamedVasyuninInterval :=
{
  h := 1
  k := 44
  lower := (17097599/249010000)
  upper := (17147401/249010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_44_interval
}

theorem G1_45_formula : baezDuarteGramEntry 1 45 = vasyuninBEntry 1 45 := vasyuninBEntry_correct_axiom 1 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_45_eval :
    ((((58483207/867930000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 45) ∧
    (vasyuninBEntry 1 45 ≤ (((58656793/867930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_145_formula_bound
  constructor <;> linarith

theorem G1_45_interval :
    ((((58483207/867930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 45) ∧
    (baezDuarteGramEntry 1 45 ≤ (((58656793/867930000) : ℚ) : ℝ)) := by
  rw [G1_45_formula]
  exact vasyuninBEntry_1_45_eval

def interval_1_45 : NamedVasyuninInterval :=
{
  h := 1
  k := 45
  lower := (58483207/867930000)
  upper := (58656793/867930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_45_interval
}

theorem G1_46_formula : baezDuarteGramEntry 1 46 = vasyuninBEntry 1 46 := vasyuninBEntry_correct_axiom 1 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_46_eval :
    ((((25791013/389870000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 46) ∧
    (vasyuninBEntry 1 46 ≤ (((25868987/389870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_146_formula_bound
  constructor <;> linarith

theorem G1_46_interval :
    ((((25791013/389870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 46) ∧
    (baezDuarteGramEntry 1 46 ≤ (((25868987/389870000) : ℚ) : ℝ)) := by
  rw [G1_46_formula]
  exact vasyuninBEntry_1_46_eval

def interval_1_46 : NamedVasyuninInterval :=
{
  h := 1
  k := 46
  lower := (25791013/389870000)
  upper := (25868987/389870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_46_interval
}

theorem G1_47_formula : baezDuarteGramEntry 1 47 = vasyuninBEntry 1 47 := vasyuninBEntry_correct_axiom 1 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_47_eval :
    ((((10068503/154970000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 47) ∧
    (vasyuninBEntry 1 47 ≤ (((10099497/154970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_147_formula_bound
  constructor <;> linarith

theorem G1_47_interval :
    ((((10068503/154970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 47) ∧
    (baezDuarteGramEntry 1 47 ≤ (((10099497/154970000) : ℚ) : ℝ)) := by
  rw [G1_47_formula]
  exact vasyuninBEntry_1_47_eval

def interval_1_47 : NamedVasyuninInterval :=
{
  h := 1
  k := 47
  lower := (10068503/154970000)
  upper := (10099497/154970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_47_interval
}

theorem G1_48_formula : baezDuarteGramEntry 1 48 = vasyuninBEntry 1 48 := vasyuninBEntry_correct_axiom 1 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_48_eval :
    ((((17622393/276070000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 48) ∧
    (vasyuninBEntry 1 48 ≤ (((17677607/276070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_148_formula_bound
  constructor <;> linarith

theorem G1_48_interval :
    ((((17622393/276070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 48) ∧
    (baezDuarteGramEntry 1 48 ≤ (((17677607/276070000) : ℚ) : ℝ)) := by
  rw [G1_48_formula]
  exact vasyuninBEntry_1_48_eval

def interval_1_48 : NamedVasyuninInterval :=
{
  h := 1
  k := 48
  lower := (17622393/276070000)
  upper := (17677607/276070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_48_interval
}

theorem G1_49_formula : baezDuarteGramEntry 1 49 = vasyuninBEntry 1 49 := vasyuninBEntry_correct_axiom 1 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_49_eval :
    ((((1974977/31480000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 49) ∧
    (vasyuninBEntry 1 49 ≤ (((1981273/31480000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_149_formula_bound
  constructor <;> linarith

theorem G1_49_interval :
    ((((1974977/31480000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 49) ∧
    (baezDuarteGramEntry 1 49 ≤ (((1981273/31480000) : ℚ) : ℝ)) := by
  rw [G1_49_formula]
  exact vasyuninBEntry_1_49_eval

def interval_1_49 : NamedVasyuninInterval :=
{
  h := 1
  k := 49
  lower := (1974977/31480000)
  upper := (1981273/31480000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_49_interval
}

theorem G1_50_formula : baezDuarteGramEntry 1 50 = vasyuninBEntry 1 50 := vasyuninBEntry_correct_axiom 1 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_1_50_eval :
    ((((8232653/133470000) : ℚ) : ℝ) ≤ vasyuninBEntry 1 50) ∧
    (vasyuninBEntry 1 50 ≤ (((8259347/133470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_150_formula_bound
  constructor <;> linarith

theorem G1_50_interval :
    ((((8232653/133470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 1 50) ∧
    (baezDuarteGramEntry 1 50 ≤ (((8259347/133470000) : ℚ) : ℝ)) := by
  rw [G1_50_formula]
  exact vasyuninBEntry_1_50_eval

def interval_1_50 : NamedVasyuninInterval :=
{
  h := 1
  k := 50
  lower := (8232653/133470000)
  upper := (8259347/133470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G1_50_interval
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

theorem G2_3_formula : baezDuarteGramEntry 2 3 = vasyuninBEntry 2 3 := vasyuninBEntry_correct_axiom 2 3 (by norm_num) (by norm_num)

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

theorem G2_4_formula : baezDuarteGramEntry 2 4 = vasyuninBEntry 2 4 := vasyuninBEntry_correct_axiom 2 4 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_4_eval :
    ((((368854443/955570000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 4) ∧
    (vasyuninBEntry 2 4 ≤ (((369045557/955570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G2_5_formula : baezDuarteGramEntry 2 5 = vasyuninBEntry 2 5 := vasyuninBEntry_correct_axiom 2 5 (by norm_num) (by norm_num)

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

theorem G2_6_formula : baezDuarteGramEntry 2 6 = vasyuninBEntry 2 6 := vasyuninBEntry_correct_axiom 2 6 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_6_eval :
    ((((269206331/936690000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 6) ∧
    (vasyuninBEntry 2 6 ≤ (((269393669/936690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G2_7_formula : baezDuarteGramEntry 2 7 = vasyuninBEntry 2 7 := vasyuninBEntry_correct_axiom 2 7 (by norm_num) (by norm_num)

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

theorem G2_8_formula : baezDuarteGramEntry 2 8 = vasyuninBEntry 2 8 := vasyuninBEntry_correct_axiom 2 8 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_8_eval :
    ((((75927287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 8) ∧
    (vasyuninBEntry 2 8 ≤ (((75992713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G2_9_formula : baezDuarteGramEntry 2 9 = vasyuninBEntry 2 9 := vasyuninBEntry_correct_axiom 2 9 (by norm_num) (by norm_num)

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

theorem G2_10_formula : baezDuarteGramEntry 2 10 = vasyuninBEntry 2 10 := vasyuninBEntry_correct_axiom 2 10 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_10_eval :
    ((((64257239/327610000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 10) ∧
    (vasyuninBEntry 2 10 ≤ (((64322761/327610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G2_11_formula : baezDuarteGramEntry 2 11 = vasyuninBEntry 2 11 := vasyuninBEntry_correct_axiom 2 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_11_eval :
    ((((146398607/813930000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 11) ∧
    (vasyuninBEntry 2 11 ≤ (((146561393/813930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_211_formula_bound
  constructor <;> linarith

theorem G2_11_interval :
    ((((146398607/813930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 11) ∧
    (baezDuarteGramEntry 2 11 ≤ (((146561393/813930000) : ℚ) : ℝ)) := by
  rw [G2_11_formula]
  exact vasyuninBEntry_2_11_eval

def interval_2_11 : NamedVasyuninInterval :=
{
  h := 2
  k := 11
  lower := (146398607/813930000)
  upper := (146561393/813930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_11_interval
}

theorem G2_12_formula : baezDuarteGramEntry 2 12 = vasyuninBEntry 2 12 := vasyuninBEntry_correct_axiom 2 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_12_eval :
    ((((69074523/404770000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 12) ∧
    (vasyuninBEntry 2 12 ≤ (((69155477/404770000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 6 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_12_interval :
    ((((69074523/404770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 12) ∧
    (baezDuarteGramEntry 2 12 ≤ (((69155477/404770000) : ℚ) : ℝ)) := by
  rw [G2_12_formula]
  exact vasyuninBEntry_2_12_eval

def interval_2_12 : NamedVasyuninInterval :=
{
  h := 2
  k := 12
  lower := (69074523/404770000)
  upper := (69155477/404770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_12_interval
}

theorem G2_13_formula : baezDuarteGramEntry 2 13 = vasyuninBEntry 2 13 := vasyuninBEntry_correct_axiom 2 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_13_eval :
    ((((104703999/660010000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 13) ∧
    (vasyuninBEntry 2 13 ≤ (((104836001/660010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_213_formula_bound
  constructor <;> linarith

theorem G2_13_interval :
    ((((104703999/660010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 13) ∧
    (baezDuarteGramEntry 2 13 ≤ (((104836001/660010000) : ℚ) : ℝ)) := by
  rw [G2_13_formula]
  exact vasyuninBEntry_2_13_eval

def interval_2_13 : NamedVasyuninInterval :=
{
  h := 2
  k := 13
  lower := (104703999/660010000)
  upper := (104836001/660010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_13_interval
}

theorem G2_14_formula : baezDuarteGramEntry 2 14 = vasyuninBEntry 2 14 := vasyuninBEntry_correct_axiom 2 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_14_eval :
    ((((77688731/512690000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 14) ∧
    (vasyuninBEntry 2 14 ≤ (((77791269/512690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 7 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_14_interval :
    ((((77688731/512690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 14) ∧
    (baezDuarteGramEntry 2 14 ≤ (((77791269/512690000) : ℚ) : ℝ)) := by
  rw [G2_14_formula]
  exact vasyuninBEntry_2_14_eval

def interval_2_14 : NamedVasyuninInterval :=
{
  h := 2
  k := 14
  lower := (77688731/512690000)
  upper := (77791269/512690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_14_interval
}

theorem G2_15_formula : baezDuarteGramEntry 2 15 = vasyuninBEntry 2 15 := vasyuninBEntry_correct_axiom 2 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_15_eval :
    ((((8406591/59090000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 15) ∧
    (vasyuninBEntry 2 15 ≤ (((8418409/59090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_215_formula_bound
  constructor <;> linarith

theorem G2_15_interval :
    ((((8406591/59090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 15) ∧
    (baezDuarteGramEntry 2 15 ≤ (((8418409/59090000) : ℚ) : ℝ)) := by
  rw [G2_15_formula]
  exact vasyuninBEntry_2_15_eval

def interval_2_15 : NamedVasyuninInterval :=
{
  h := 2
  k := 15
  lower := (8406591/59090000)
  upper := (8418409/59090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_15_interval
}

theorem G2_16_formula : baezDuarteGramEntry 2 16 = vasyuninBEntry 2 16 := vasyuninBEntry_correct_axiom 2 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_16_eval :
    ((((7473279/54710000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 16) ∧
    (vasyuninBEntry 2 16 ≤ (((7484221/54710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 8 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_16_interval :
    ((((7473279/54710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 16) ∧
    (baezDuarteGramEntry 2 16 ≤ (((7484221/54710000) : ℚ) : ℝ)) := by
  rw [G2_16_formula]
  exact vasyuninBEntry_2_16_eval

def interval_2_16 : NamedVasyuninInterval :=
{
  h := 2
  k := 16
  lower := (7473279/54710000)
  upper := (7484221/54710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_16_interval
}

theorem G2_17_formula : baezDuarteGramEntry 2 17 = vasyuninBEntry 2 17 := vasyuninBEntry_correct_axiom 2 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_17_eval :
    ((((856697/6630000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 17) ∧
    (vasyuninBEntry 2 17 ≤ (((858023/6630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_217_formula_bound
  constructor <;> linarith

theorem G2_17_interval :
    ((((856697/6630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 17) ∧
    (baezDuarteGramEntry 2 17 ≤ (((858023/6630000) : ℚ) : ℝ)) := by
  rw [G2_17_formula]
  exact vasyuninBEntry_2_17_eval

def interval_2_17 : NamedVasyuninInterval :=
{
  h := 2
  k := 17
  lower := (856697/6630000)
  upper := (858023/6630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_17_interval
}

theorem G2_18_formula : baezDuarteGramEntry 2 18 = vasyuninBEntry 2 18 := vasyuninBEntry_correct_axiom 2 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_18_eval :
    ((((40807243/327570000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 18) ∧
    (vasyuninBEntry 2 18 ≤ (((40872757/327570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 9 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_18_interval :
    ((((40807243/327570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 18) ∧
    (baezDuarteGramEntry 2 18 ≤ (((40872757/327570000) : ℚ) : ℝ)) := by
  rw [G2_18_formula]
  exact vasyuninBEntry_2_18_eval

def interval_2_18 : NamedVasyuninInterval :=
{
  h := 2
  k := 18
  lower := (40807243/327570000)
  upper := (40872757/327570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_18_interval
}

theorem G2_19_formula : baezDuarteGramEntry 2 19 = vasyuninBEntry 2 19 := vasyuninBEntry_correct_axiom 2 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_19_eval :
    ((((37213607/313930000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 19) ∧
    (vasyuninBEntry 2 19 ≤ (((37276393/313930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_219_formula_bound
  constructor <;> linarith

theorem G2_19_interval :
    ((((37213607/313930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 19) ∧
    (baezDuarteGramEntry 2 19 ≤ (((37276393/313930000) : ℚ) : ℝ)) := by
  rw [G2_19_formula]
  exact vasyuninBEntry_2_19_eval

def interval_2_19 : NamedVasyuninInterval :=
{
  h := 2
  k := 19
  lower := (37213607/313930000)
  upper := (37276393/313930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_19_interval
}

theorem G2_20_formula : baezDuarteGramEntry 2 20 = vasyuninBEntry 2 20 := vasyuninBEntry_correct_axiom 2 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_20_eval :
    ((((40714493/355070000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 20) ∧
    (vasyuninBEntry 2 20 ≤ (((40785507/355070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 10 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_20_interval :
    ((((40714493/355070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 20) ∧
    (baezDuarteGramEntry 2 20 ≤ (((40785507/355070000) : ℚ) : ℝ)) := by
  rw [G2_20_formula]
  exact vasyuninBEntry_2_20_eval

def interval_2_20 : NamedVasyuninInterval :=
{
  h := 2
  k := 20
  lower := (40714493/355070000)
  upper := (40785507/355070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_20_interval
}

theorem G2_21_formula : baezDuarteGramEntry 2 21 = vasyuninBEntry 2 21 := vasyuninBEntry_correct_axiom 2 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_21_eval :
    ((((36416783/332170000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 21) ∧
    (vasyuninBEntry 2 21 ≤ (((36483217/332170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_221_formula_bound
  constructor <;> linarith

theorem G2_21_interval :
    ((((36416783/332170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 21) ∧
    (baezDuarteGramEntry 2 21 ≤ (((36483217/332170000) : ℚ) : ℝ)) := by
  rw [G2_21_formula]
  exact vasyuninBEntry_2_21_eval

def interval_2_21 : NamedVasyuninInterval :=
{
  h := 2
  k := 21
  lower := (36416783/332170000)
  upper := (36483217/332170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_21_interval
}

theorem G2_22_formula : baezDuarteGramEntry 2 22 = vasyuninBEntry 2 22 := vasyuninBEntry_correct_axiom 2 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_22_eval :
    ((((47010793/442070000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 22) ∧
    (vasyuninBEntry 2 22 ≤ (((47099207/442070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 11 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_22_interval :
    ((((47010793/442070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 22) ∧
    (baezDuarteGramEntry 2 22 ≤ (((47099207/442070000) : ℚ) : ℝ)) := by
  rw [G2_22_formula]
  exact vasyuninBEntry_2_22_eval

def interval_2_22 : NamedVasyuninInterval :=
{
  h := 2
  k := 22
  lower := (47010793/442070000)
  upper := (47099207/442070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_22_interval
}

theorem G2_23_formula : baezDuarteGramEntry 2 23 = vasyuninBEntry 2 23 := vasyuninBEntry_correct_axiom 2 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_23_eval :
    ((((100961091/989090000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 23) ∧
    (vasyuninBEntry 2 23 ≤ (((101158909/989090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_223_formula_bound
  constructor <;> linarith

theorem G2_23_interval :
    ((((100961091/989090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 23) ∧
    (baezDuarteGramEntry 2 23 ≤ (((101158909/989090000) : ℚ) : ℝ)) := by
  rw [G2_23_formula]
  exact vasyuninBEntry_2_23_eval

def interval_2_23 : NamedVasyuninInterval :=
{
  h := 2
  k := 23
  lower := (100961091/989090000)
  upper := (101158909/989090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_23_interval
}

theorem G2_24_formula : baezDuarteGramEntry 2 24 = vasyuninBEntry 2 24 := vasyuninBEntry_correct_axiom 2 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_24_eval :
    ((((23820997/240030000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 24) ∧
    (vasyuninBEntry 2 24 ≤ (((23869003/240030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 12 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_24_interval :
    ((((23820997/240030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 24) ∧
    (baezDuarteGramEntry 2 24 ≤ (((23869003/240030000) : ℚ) : ℝ)) := by
  rw [G2_24_formula]
  exact vasyuninBEntry_2_24_eval

def interval_2_24 : NamedVasyuninInterval :=
{
  h := 2
  k := 24
  lower := (23820997/240030000)
  upper := (23869003/240030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_24_interval
}

theorem G2_25_formula : baezDuarteGramEntry 2 25 = vasyuninBEntry 2 25 := vasyuninBEntry_correct_axiom 2 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_25_eval :
    ((((42475557/444430000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 25) ∧
    (vasyuninBEntry 2 25 ≤ (((42564443/444430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_225_formula_bound
  constructor <;> linarith

theorem G2_25_interval :
    ((((42475557/444430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 25) ∧
    (baezDuarteGramEntry 2 25 ≤ (((42564443/444430000) : ℚ) : ℝ)) := by
  rw [G2_25_formula]
  exact vasyuninBEntry_2_25_eval

def interval_2_25 : NamedVasyuninInterval :=
{
  h := 2
  k := 25
  lower := (42475557/444430000)
  upper := (42564443/444430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_25_interval
}

theorem G2_26_formula : baezDuarteGramEntry 2 26 = vasyuninBEntry 2 26 := vasyuninBEntry_correct_axiom 2 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_26_eval :
    ((((26776241/287590000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 26) ∧
    (vasyuninBEntry 2 26 ≤ (((26833759/287590000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 13 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_26_interval :
    ((((26776241/287590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 26) ∧
    (baezDuarteGramEntry 2 26 ≤ (((26833759/287590000) : ℚ) : ℝ)) := by
  rw [G2_26_formula]
  exact vasyuninBEntry_2_26_eval

def interval_2_26 : NamedVasyuninInterval :=
{
  h := 2
  k := 26
  lower := (26776241/287590000)
  upper := (26833759/287590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_26_interval
}

theorem G2_27_formula : baezDuarteGramEntry 2 27 = vasyuninBEntry 2 27 := vasyuninBEntry_correct_axiom 2 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_27_eval :
    ((((30266339/336610000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 27) ∧
    (vasyuninBEntry 2 27 ≤ (((30333661/336610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_227_formula_bound
  constructor <;> linarith

theorem G2_27_interval :
    ((((30266339/336610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 27) ∧
    (baezDuarteGramEntry 2 27 ≤ (((30333661/336610000) : ℚ) : ℝ)) := by
  rw [G2_27_formula]
  exact vasyuninBEntry_2_27_eval

def interval_2_27 : NamedVasyuninInterval :=
{
  h := 2
  k := 27
  lower := (30266339/336610000)
  upper := (30333661/336610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_27_interval
}

theorem G2_28_formula : baezDuarteGramEntry 2 28 = vasyuninBEntry 2 28 := vasyuninBEntry_correct_axiom 2 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_28_eval :
    ((((75094417/855830000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 28) ∧
    (vasyuninBEntry 2 28 ≤ (((75265583/855830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 14 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_28_interval :
    ((((75094417/855830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 28) ∧
    (baezDuarteGramEntry 2 28 ≤ (((75265583/855830000) : ℚ) : ℝ)) := by
  rw [G2_28_formula]
  exact vasyuninBEntry_2_28_eval

def interval_2_28 : NamedVasyuninInterval :=
{
  h := 2
  k := 28
  lower := (75094417/855830000)
  upper := (75265583/855830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_28_interval
}

theorem G2_29_formula : baezDuarteGramEntry 2 29 = vasyuninBEntry 2 29 := vasyuninBEntry_correct_axiom 2 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_29_eval :
    ((((37485869/441310000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 29) ∧
    (vasyuninBEntry 2 29 ≤ (((37574131/441310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_229_formula_bound
  constructor <;> linarith

theorem G2_29_interval :
    ((((37485869/441310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 29) ∧
    (baezDuarteGramEntry 2 29 ≤ (((37574131/441310000) : ℚ) : ℝ)) := by
  rw [G2_29_formula]
  exact vasyuninBEntry_2_29_eval

def interval_2_29 : NamedVasyuninInterval :=
{
  h := 2
  k := 29
  lower := (37485869/441310000)
  upper := (37574131/441310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_29_interval
}

theorem G2_30_formula : baezDuarteGramEntry 2 30 = vasyuninBEntry 2 30 := vasyuninBEntry_correct_axiom 2 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_30_eval :
    ((((13074251/157490000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 30) ∧
    (vasyuninBEntry 2 30 ≤ (((13105749/157490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 15 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_30_interval :
    ((((13074251/157490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 30) ∧
    (baezDuarteGramEntry 2 30 ≤ (((13105749/157490000) : ℚ) : ℝ)) := by
  rw [G2_30_formula]
  exact vasyuninBEntry_2_30_eval

def interval_2_30 : NamedVasyuninInterval :=
{
  h := 2
  k := 30
  lower := (13074251/157490000)
  upper := (13105749/157490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_30_interval
}

theorem G2_31_formula : baezDuarteGramEntry 2 31 = vasyuninBEntry 2 31 := vasyuninBEntry_correct_axiom 2 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_31_eval :
    ((((10839041/134590000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 31) ∧
    (vasyuninBEntry 2 31 ≤ (((10865959/134590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_231_formula_bound
  constructor <;> linarith

theorem G2_31_interval :
    ((((10839041/134590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 31) ∧
    (baezDuarteGramEntry 2 31 ≤ (((10865959/134590000) : ℚ) : ℝ)) := by
  rw [G2_31_formula]
  exact vasyuninBEntry_2_31_eval

def interval_2_31 : NamedVasyuninInterval :=
{
  h := 2
  k := 31
  lower := (10839041/134590000)
  upper := (10865959/134590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_31_interval
}

theorem G2_32_formula : baezDuarteGramEntry 2 32 = vasyuninBEntry 2 32 := vasyuninBEntry_correct_axiom 2 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_32_eval :
    ((((74884983/950170000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 32) ∧
    (vasyuninBEntry 2 32 ≤ (((75075017/950170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 16 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_32_interval :
    ((((74884983/950170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 32) ∧
    (baezDuarteGramEntry 2 32 ≤ (((75075017/950170000) : ℚ) : ℝ)) := by
  rw [G2_32_formula]
  exact vasyuninBEntry_2_32_eval

def interval_2_32 : NamedVasyuninInterval :=
{
  h := 2
  k := 32
  lower := (74884983/950170000)
  upper := (75075017/950170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_32_interval
}

theorem G2_33_formula : baezDuarteGramEntry 2 33 = vasyuninBEntry 2 33 := vasyuninBEntry_correct_axiom 2 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_33_eval :
    ((((76350321/996790000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 33) ∧
    (vasyuninBEntry 2 33 ≤ (((76549679/996790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_233_formula_bound
  constructor <;> linarith

theorem G2_33_interval :
    ((((76350321/996790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 33) ∧
    (baezDuarteGramEntry 2 33 ≤ (((76549679/996790000) : ℚ) : ℝ)) := by
  rw [G2_33_formula]
  exact vasyuninBEntry_2_33_eval

def interval_2_33 : NamedVasyuninInterval :=
{
  h := 2
  k := 33
  lower := (76350321/996790000)
  upper := (76549679/996790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_33_interval
}

theorem G2_34_formula : baezDuarteGramEntry 2 34 = vasyuninBEntry 2 34 := vasyuninBEntry_correct_axiom 2 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_34_eval :
    ((((3445409/45910000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 34) ∧
    (vasyuninBEntry 2 34 ≤ (((3454591/45910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_34_interval :
    ((((3445409/45910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 34) ∧
    (baezDuarteGramEntry 2 34 ≤ (((3454591/45910000) : ℚ) : ℝ)) := by
  rw [G2_34_formula]
  exact vasyuninBEntry_2_34_eval

def interval_2_34 : NamedVasyuninInterval :=
{
  h := 2
  k := 34
  lower := (3445409/45910000)
  upper := (3454591/45910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_34_interval
}

theorem G2_35_formula : baezDuarteGramEntry 2 35 = vasyuninBEntry 2 35 := vasyuninBEntry_correct_axiom 2 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_35_eval :
    ((((57311551/784490000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 35) ∧
    (vasyuninBEntry 2 35 ≤ (((57468449/784490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_235_formula_bound
  constructor <;> linarith

theorem G2_35_interval :
    ((((57311551/784490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 35) ∧
    (baezDuarteGramEntry 2 35 ≤ (((57468449/784490000) : ℚ) : ℝ)) := by
  rw [G2_35_formula]
  exact vasyuninBEntry_2_35_eval

def interval_2_35 : NamedVasyuninInterval :=
{
  h := 2
  k := 35
  lower := (57311551/784490000)
  upper := (57468449/784490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_35_interval
}

theorem G2_36_formula : baezDuarteGramEntry 2 36 = vasyuninBEntry 2 36 := vasyuninBEntry_correct_axiom 2 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_36_eval :
    ((((6770551/94490000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 36) ∧
    (vasyuninBEntry 2 36 ≤ (((6789449/94490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_18_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 18 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_36_interval :
    ((((6770551/94490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 36) ∧
    (baezDuarteGramEntry 2 36 ≤ (((6789449/94490000) : ℚ) : ℝ)) := by
  rw [G2_36_formula]
  exact vasyuninBEntry_2_36_eval

def interval_2_36 : NamedVasyuninInterval :=
{
  h := 2
  k := 36
  lower := (6770551/94490000)
  upper := (6789449/94490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_36_interval
}

theorem G2_37_formula : baezDuarteGramEntry 2 37 = vasyuninBEntry 2 37 := vasyuninBEntry_correct_axiom 2 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_37_eval :
    ((((12552031/179690000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 37) ∧
    (vasyuninBEntry 2 37 ≤ (((12587969/179690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_237_formula_bound
  constructor <;> linarith

theorem G2_37_interval :
    ((((12552031/179690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 37) ∧
    (baezDuarteGramEntry 2 37 ≤ (((12587969/179690000) : ℚ) : ℝ)) := by
  rw [G2_37_formula]
  exact vasyuninBEntry_2_37_eval

def interval_2_37 : NamedVasyuninInterval :=
{
  h := 2
  k := 37
  lower := (12552031/179690000)
  upper := (12587969/179690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_37_interval
}

theorem G2_38_formula : baezDuarteGramEntry 2 38 = vasyuninBEntry 2 38 := vasyuninBEntry_correct_axiom 2 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_38_eval :
    ((((1130851/16490000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 38) ∧
    (vasyuninBEntry 2 38 ≤ (((1134149/16490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_38_interval :
    ((((1130851/16490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 38) ∧
    (baezDuarteGramEntry 2 38 ≤ (((1134149/16490000) : ℚ) : ℝ)) := by
  rw [G2_38_formula]
  exact vasyuninBEntry_2_38_eval

def interval_2_38 : NamedVasyuninInterval :=
{
  h := 2
  k := 38
  lower := (1130851/16490000)
  upper := (1134149/16490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_38_interval
}

theorem G2_39_formula : baezDuarteGramEntry 2 39 = vasyuninBEntry 2 39 := vasyuninBEntry_correct_axiom 2 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_39_eval :
    ((((10803861/161390000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 39) ∧
    (vasyuninBEntry 2 39 ≤ (((10836139/161390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_239_formula_bound
  constructor <;> linarith

theorem G2_39_interval :
    ((((10803861/161390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 39) ∧
    (baezDuarteGramEntry 2 39 ≤ (((10836139/161390000) : ℚ) : ℝ)) := by
  rw [G2_39_formula]
  exact vasyuninBEntry_2_39_eval

def interval_2_39 : NamedVasyuninInterval :=
{
  h := 2
  k := 39
  lower := (10803861/161390000)
  upper := (10836139/161390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_39_interval
}

theorem G2_40_formula : baezDuarteGramEntry 2 40 = vasyuninBEntry 2 40 := vasyuninBEntry_correct_axiom 2 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_40_eval :
    ((((59749163/908370000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 40) ∧
    (vasyuninBEntry 2 40 ≤ (((59930837/908370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 20 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_40_interval :
    ((((59749163/908370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 40) ∧
    (baezDuarteGramEntry 2 40 ≤ (((59930837/908370000) : ℚ) : ℝ)) := by
  rw [G2_40_formula]
  exact vasyuninBEntry_2_40_eval

def interval_2_40 : NamedVasyuninInterval :=
{
  h := 2
  k := 40
  lower := (59749163/908370000)
  upper := (59930837/908370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_40_interval
}

theorem G2_41_formula : baezDuarteGramEntry 2 41 = vasyuninBEntry 2 41 := vasyuninBEntry_correct_axiom 2 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_41_eval :
    ((((62362987/970130000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 41) ∧
    (vasyuninBEntry 2 41 ≤ (((62557013/970130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_241_formula_bound
  constructor <;> linarith

theorem G2_41_interval :
    ((((62362987/970130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 41) ∧
    (baezDuarteGramEntry 2 41 ≤ (((62557013/970130000) : ℚ) : ℝ)) := by
  rw [G2_41_formula]
  exact vasyuninBEntry_2_41_eval

def interval_2_41 : NamedVasyuninInterval :=
{
  h := 2
  k := 41
  lower := (62362987/970130000)
  upper := (62557013/970130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_41_interval
}

theorem G2_42_formula : baezDuarteGramEntry 2 42 = vasyuninBEntry 2 42 := vasyuninBEntry_correct_axiom 2 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_42_eval :
    ((((5320583/84170000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 42) ∧
    (vasyuninBEntry 2 42 ≤ (((5337417/84170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 21 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_42_interval :
    ((((5320583/84170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 42) ∧
    (baezDuarteGramEntry 2 42 ≤ (((5337417/84170000) : ℚ) : ℝ)) := by
  rw [G2_42_formula]
  exact vasyuninBEntry_2_42_eval

def interval_2_42 : NamedVasyuninInterval :=
{
  h := 2
  k := 42
  lower := (5320583/84170000)
  upper := (5337417/84170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_42_interval
}

theorem G2_43_formula : baezDuarteGramEntry 2 43 = vasyuninBEntry 2 43 := vasyuninBEntry_correct_axiom 2 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_43_eval :
    ((((8678467/140330000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 43) ∧
    (vasyuninBEntry 2 43 ≤ (((8706533/140330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_243_formula_bound
  constructor <;> linarith

theorem G2_43_interval :
    ((((8678467/140330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 43) ∧
    (baezDuarteGramEntry 2 43 ≤ (((8706533/140330000) : ℚ) : ℝ)) := by
  rw [G2_43_formula]
  exact vasyuninBEntry_2_43_eval

def interval_2_43 : NamedVasyuninInterval :=
{
  h := 2
  k := 43
  lower := (8678467/140330000)
  upper := (8706533/140330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_43_interval
}

theorem G2_44_formula : baezDuarteGramEntry 2 44 = vasyuninBEntry 2 44 := vasyuninBEntry_correct_axiom 2 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_44_eval :
    ((((3671467/60330000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 44) ∧
    (vasyuninBEntry 2 44 ≤ (((3683533/60330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 22 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_44_interval :
    ((((3671467/60330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 44) ∧
    (baezDuarteGramEntry 2 44 ≤ (((3683533/60330000) : ℚ) : ℝ)) := by
  rw [G2_44_formula]
  exact vasyuninBEntry_2_44_eval

def interval_2_44 : NamedVasyuninInterval :=
{
  h := 2
  k := 44
  lower := (3671467/60330000)
  upper := (3683533/60330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_44_interval
}

theorem G2_45_formula : baezDuarteGramEntry 2 45 = vasyuninBEntry 2 45 := vasyuninBEntry_correct_axiom 2 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_45_eval :
    ((((56764751/952490000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 45) ∧
    (vasyuninBEntry 2 45 ≤ (((56955249/952490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_245_formula_bound
  constructor <;> linarith

theorem G2_45_interval :
    ((((56764751/952490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 45) ∧
    (baezDuarteGramEntry 2 45 ≤ (((56955249/952490000) : ℚ) : ℝ)) := by
  rw [G2_45_formula]
  exact vasyuninBEntry_2_45_eval

def interval_2_45 : NamedVasyuninInterval :=
{
  h := 2
  k := 45
  lower := (56764751/952490000)
  upper := (56955249/952490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_45_interval
}

theorem G2_46_formula : baezDuarteGramEntry 2 46 = vasyuninBEntry 2 46 := vasyuninBEntry_correct_axiom 2 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_46_eval :
    ((((28825879/491210000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 46) ∧
    (vasyuninBEntry 2 46 ≤ (((28924121/491210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_46_interval :
    ((((28825879/491210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 46) ∧
    (baezDuarteGramEntry 2 46 ≤ (((28924121/491210000) : ℚ) : ℝ)) := by
  rw [G2_46_formula]
  exact vasyuninBEntry_2_46_eval

def interval_2_46 : NamedVasyuninInterval :=
{
  h := 2
  k := 46
  lower := (28825879/491210000)
  upper := (28924121/491210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_46_interval
}

theorem G2_47_formula : baezDuarteGramEntry 2 47 = vasyuninBEntry 2 47 := vasyuninBEntry_correct_axiom 2 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_47_eval :
    ((((1821633/31670000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 47) ∧
    (vasyuninBEntry 2 47 ≤ (((1827967/31670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_247_formula_bound
  constructor <;> linarith

theorem G2_47_interval :
    ((((1821633/31670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 47) ∧
    (baezDuarteGramEntry 2 47 ≤ (((1827967/31670000) : ℚ) : ℝ)) := by
  rw [G2_47_formula]
  exact vasyuninBEntry_2_47_eval

def interval_2_47 : NamedVasyuninInterval :=
{
  h := 2
  k := 47
  lower := (1821633/31670000)
  upper := (1827967/31670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_47_interval
}

theorem G2_48_formula : baezDuarteGramEntry 2 48 = vasyuninBEntry 2 48 := vasyuninBEntry_correct_axiom 2 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_48_eval :
    ((((51469181/908190000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 48) ∧
    (vasyuninBEntry 2 48 ≤ (((51650819/908190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 24 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_48_interval :
    ((((51469181/908190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 48) ∧
    (baezDuarteGramEntry 2 48 ≤ (((51650819/908190000) : ℚ) : ℝ)) := by
  rw [G2_48_formula]
  exact vasyuninBEntry_2_48_eval

def interval_2_48 : NamedVasyuninInterval :=
{
  h := 2
  k := 48
  lower := (51469181/908190000)
  upper := (51650819/908190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_48_interval
}

theorem G2_49_formula : baezDuarteGramEntry 2 49 = vasyuninBEntry 2 49 := vasyuninBEntry_correct_axiom 2 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_49_eval :
    ((((54961137/988630000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 49) ∧
    (vasyuninBEntry 2 49 ≤ (((55158863/988630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_249_formula_bound
  constructor <;> linarith

theorem G2_49_interval :
    ((((54961137/988630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 49) ∧
    (baezDuarteGramEntry 2 49 ≤ (((55158863/988630000) : ℚ) : ℝ)) := by
  rw [G2_49_formula]
  exact vasyuninBEntry_2_49_eval

def interval_2_49 : NamedVasyuninInterval :=
{
  h := 2
  k := 49
  lower := (54961137/988630000)
  upper := (55158863/988630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_49_interval
}

theorem G2_50_formula : baezDuarteGramEntry 2 50 = vasyuninBEntry 2 50 := vasyuninBEntry_correct_axiom 2 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_2_50_eval :
    ((((2106157/38430000) : ℚ) : ℝ) ≤ vasyuninBEntry 2 50) ∧
    (vasyuninBEntry 2 50 ≤ (((2113843/38430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G2_50_interval :
    ((((2106157/38430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 2 50) ∧
    (baezDuarteGramEntry 2 50 ≤ (((2113843/38430000) : ℚ) : ℝ)) := by
  rw [G2_50_formula]
  exact vasyuninBEntry_2_50_eval

def interval_2_50 : NamedVasyuninInterval :=
{
  h := 2
  k := 50
  lower := (2106157/38430000)
  upper := (2113843/38430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G2_50_interval
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

theorem G3_4_formula : baezDuarteGramEntry 3 4 = vasyuninBEntry 3 4 := vasyuninBEntry_correct_axiom 3 4 (by norm_num) (by norm_num)

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

theorem G3_5_formula : baezDuarteGramEntry 3 5 = vasyuninBEntry 3 5 := vasyuninBEntry_correct_axiom 3 5 (by norm_num) (by norm_num)

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

theorem G3_6_formula : baezDuarteGramEntry 3 6 = vasyuninBEntry 3 6 := vasyuninBEntry_correct_axiom 3 6 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_6_eval :
    ((((45200433/175670000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 6) ∧
    (vasyuninBEntry 3 6 ≤ (((45235567/175670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 3 (by norm_num) (by norm_num) (by norm_num)
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

theorem G3_7_formula : baezDuarteGramEntry 3 7 = vasyuninBEntry 3 7 := vasyuninBEntry_correct_axiom 3 7 (by norm_num) (by norm_num)

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

theorem G3_8_formula : baezDuarteGramEntry 3 8 = vasyuninBEntry 3 8 := vasyuninBEntry_correct_axiom 3 8 (by norm_num) (by norm_num)

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

theorem G3_9_formula : baezDuarteGramEntry 3 9 = vasyuninBEntry 3 9 := vasyuninBEntry_correct_axiom 3 9 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_9_eval :
    ((((124245143/648570000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 9) ∧
    (vasyuninBEntry 3 9 ≤ (((124374857/648570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 3 (by norm_num) (by norm_num) (by norm_num)
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

theorem G3_10_formula : baezDuarteGramEntry 3 10 = vasyuninBEntry 3 10 := vasyuninBEntry_correct_axiom 3 10 (by norm_num) (by norm_num)

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

theorem G3_11_formula : baezDuarteGramEntry 3 11 = vasyuninBEntry 3 11 := vasyuninBEntry_correct_axiom 3 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_11_eval :
    ((((142731359/886410000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 11) ∧
    (vasyuninBEntry 3 11 ≤ (((142908641/886410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_311_formula_bound
  constructor <;> linarith

theorem G3_11_interval :
    ((((142731359/886410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 11) ∧
    (baezDuarteGramEntry 3 11 ≤ (((142908641/886410000) : ℚ) : ℝ)) := by
  rw [G3_11_formula]
  exact vasyuninBEntry_3_11_eval

def interval_3_11 : NamedVasyuninInterval :=
{
  h := 3
  k := 11
  lower := (142731359/886410000)
  upper := (142908641/886410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_11_interval
}

theorem G3_12_formula : baezDuarteGramEntry 3 12 = vasyuninBEntry 3 12 := vasyuninBEntry_correct_axiom 3 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_12_eval :
    ((((50607287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 12) ∧
    (vasyuninBEntry 3 12 ≤ (((50672713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_12_interval :
    ((((50607287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 12) ∧
    (baezDuarteGramEntry 3 12 ≤ (((50672713/327130000) : ℚ) : ℝ)) := by
  rw [G3_12_formula]
  exact vasyuninBEntry_3_12_eval

def interval_3_12 : NamedVasyuninInterval :=
{
  h := 3
  k := 12
  lower := (50607287/327130000)
  upper := (50672713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_12_interval
}

theorem G3_13_formula : baezDuarteGramEntry 3 13 = vasyuninBEntry 3 13 := vasyuninBEntry_correct_axiom 3 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_13_eval :
    ((((50979311/356890000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 13) ∧
    (vasyuninBEntry 3 13 ≤ (((51050689/356890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_313_formula_bound
  constructor <;> linarith

theorem G3_13_interval :
    ((((50979311/356890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 13) ∧
    (baezDuarteGramEntry 3 13 ≤ (((51050689/356890000) : ℚ) : ℝ)) := by
  rw [G3_13_formula]
  exact vasyuninBEntry_3_13_eval

def interval_3_13 : NamedVasyuninInterval :=
{
  h := 3
  k := 13
  lower := (50979311/356890000)
  upper := (51050689/356890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_13_interval
}

theorem G3_14_formula : baezDuarteGramEntry 3 14 = vasyuninBEntry 3 14 := vasyuninBEntry_correct_axiom 3 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_14_eval :
    ((((110508283/817170000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 14) ∧
    (vasyuninBEntry 3 14 ≤ (((110671717/817170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_314_formula_bound
  constructor <;> linarith

theorem G3_14_interval :
    ((((110508283/817170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 14) ∧
    (baezDuarteGramEntry 3 14 ≤ (((110671717/817170000) : ℚ) : ℝ)) := by
  rw [G3_14_formula]
  exact vasyuninBEntry_3_14_eval

def interval_3_14 : NamedVasyuninInterval :=
{
  h := 3
  k := 14
  lower := (110508283/817170000)
  upper := (110671717/817170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_14_interval
}

theorem G3_15_formula : baezDuarteGramEntry 3 15 = vasyuninBEntry 3 15 := vasyuninBEntry_correct_axiom 3 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_15_eval :
    ((((42827239/327610000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 15) ∧
    (vasyuninBEntry 3 15 ≤ (((42892761/327610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_15_interval :
    ((((42827239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 15) ∧
    (baezDuarteGramEntry 3 15 ≤ (((42892761/327610000) : ℚ) : ℝ)) := by
  rw [G3_15_formula]
  exact vasyuninBEntry_3_15_eval

def interval_3_15 : NamedVasyuninInterval :=
{
  h := 3
  k := 15
  lower := (42827239/327610000)
  upper := (42892761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_15_interval
}

theorem G3_16_formula : baezDuarteGramEntry 3 16 = vasyuninBEntry 3 16 := vasyuninBEntry_correct_axiom 3 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_16_eval :
    ((((19793853/161470000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 16) ∧
    (vasyuninBEntry 3 16 ≤ (((19826147/161470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_316_formula_bound
  constructor <;> linarith

theorem G3_16_interval :
    ((((19793853/161470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 16) ∧
    (baezDuarteGramEntry 3 16 ≤ (((19826147/161470000) : ℚ) : ℝ)) := by
  rw [G3_16_formula]
  exact vasyuninBEntry_3_16_eval

def interval_3_16 : NamedVasyuninInterval :=
{
  h := 3
  k := 16
  lower := (19793853/161470000)
  upper := (19826147/161470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_16_interval
}

theorem G3_17_formula : baezDuarteGramEntry 3 17 = vasyuninBEntry 3 17 := vasyuninBEntry_correct_axiom 3 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_17_eval :
    ((((6694909/57160000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 17) ∧
    (vasyuninBEntry 3 17 ≤ (((6706341/57160000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_317_formula_bound
  constructor <;> linarith

theorem G3_17_interval :
    ((((6694909/57160000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 17) ∧
    (baezDuarteGramEntry 3 17 ≤ (((6706341/57160000) : ℚ) : ℝ)) := by
  rw [G3_17_formula]
  exact vasyuninBEntry_3_17_eval

def interval_3_17 : NamedVasyuninInterval :=
{
  h := 3
  k := 17
  lower := (6694909/57160000)
  upper := (6706341/57160000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_17_interval
}

theorem G3_18_formula : baezDuarteGramEntry 3 18 = vasyuninBEntry 3 18 := vasyuninBEntry_correct_axiom 3 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_18_eval :
    ((((9472921/83290000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 18) ∧
    (vasyuninBEntry 3 18 ≤ (((9489579/83290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 6 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_18_interval :
    ((((9472921/83290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 18) ∧
    (baezDuarteGramEntry 3 18 ≤ (((9489579/83290000) : ℚ) : ℝ)) := by
  rw [G3_18_formula]
  exact vasyuninBEntry_3_18_eval

def interval_3_18 : NamedVasyuninInterval :=
{
  h := 3
  k := 18
  lower := (9472921/83290000)
  upper := (9489579/83290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_18_interval
}

theorem G3_19_formula : baezDuarteGramEntry 3 19 = vasyuninBEntry 3 19 := vasyuninBEntry_correct_axiom 3 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_19_eval :
    ((((9353321/86790000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 19) ∧
    (vasyuninBEntry 3 19 ≤ (((9370679/86790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_319_formula_bound
  constructor <;> linarith

theorem G3_19_interval :
    ((((9353321/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 19) ∧
    (baezDuarteGramEntry 3 19 ≤ (((9370679/86790000) : ℚ) : ℝ)) := by
  rw [G3_19_formula]
  exact vasyuninBEntry_3_19_eval

def interval_3_19 : NamedVasyuninInterval :=
{
  h := 3
  k := 19
  lower := (9353321/86790000)
  upper := (9370679/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_19_interval
}

theorem G3_20_formula : baezDuarteGramEntry 3 20 = vasyuninBEntry 3 20 := vasyuninBEntry_correct_axiom 3 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_20_eval :
    ((((37633689/363110000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 20) ∧
    (vasyuninBEntry 3 20 ≤ (((37706311/363110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_320_formula_bound
  constructor <;> linarith

theorem G3_20_interval :
    ((((37633689/363110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 20) ∧
    (baezDuarteGramEntry 3 20 ≤ (((37706311/363110000) : ℚ) : ℝ)) := by
  rw [G3_20_formula]
  exact vasyuninBEntry_3_20_eval

def interval_3_20 : NamedVasyuninInterval :=
{
  h := 3
  k := 20
  lower := (37633689/363110000)
  upper := (37706311/363110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_20_interval
}

theorem G3_21_formula : baezDuarteGramEntry 3 21 = vasyuninBEntry 3 21 := vasyuninBEntry_correct_axiom 3 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_21_eval :
    ((((95535399/946010000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 21) ∧
    (vasyuninBEntry 3 21 ≤ (((95724601/946010000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 7 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_21_interval :
    ((((95535399/946010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 21) ∧
    (baezDuarteGramEntry 3 21 ≤ (((95724601/946010000) : ℚ) : ℝ)) := by
  rw [G3_21_formula]
  exact vasyuninBEntry_3_21_eval

def interval_3_21 : NamedVasyuninInterval :=
{
  h := 3
  k := 21
  lower := (95535399/946010000)
  upper := (95724601/946010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_21_interval
}

theorem G3_22_formula : baezDuarteGramEntry 3 22 = vasyuninBEntry 3 22 := vasyuninBEntry_correct_axiom 3 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_22_eval :
    ((((68828611/713890000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 22) ∧
    (vasyuninBEntry 3 22 ≤ (((68971389/713890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_322_formula_bound
  constructor <;> linarith

theorem G3_22_interval :
    ((((68828611/713890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 22) ∧
    (baezDuarteGramEntry 3 22 ≤ (((68971389/713890000) : ℚ) : ℝ)) := by
  rw [G3_22_formula]
  exact vasyuninBEntry_3_22_eval

def interval_3_22 : NamedVasyuninInterval :=
{
  h := 3
  k := 22
  lower := (68828611/713890000)
  upper := (68971389/713890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_22_interval
}

theorem G3_23_formula : baezDuarteGramEntry 3 23 = vasyuninBEntry 3 23 := vasyuninBEntry_correct_axiom 3 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_23_eval :
    ((((55640283/597170000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 23) ∧
    (vasyuninBEntry 3 23 ≤ (((55759717/597170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_323_formula_bound
  constructor <;> linarith

theorem G3_23_interval :
    ((((55640283/597170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 23) ∧
    (baezDuarteGramEntry 3 23 ≤ (((55759717/597170000) : ℚ) : ℝ)) := by
  rw [G3_23_formula]
  exact vasyuninBEntry_3_23_eval

def interval_3_23 : NamedVasyuninInterval :=
{
  h := 3
  k := 23
  lower := (55640283/597170000)
  upper := (55759717/597170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_23_interval
}

theorem G3_24_formula : baezDuarteGramEntry 3 24 = vasyuninBEntry 3 24 := vasyuninBEntry_correct_axiom 3 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_24_eval :
    ((((14941087/164130000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 24) ∧
    (vasyuninBEntry 3 24 ≤ (((14973913/164130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 8 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_24_interval :
    ((((14941087/164130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 24) ∧
    (baezDuarteGramEntry 3 24 ≤ (((14973913/164130000) : ℚ) : ℝ)) := by
  rw [G3_24_formula]
  exact vasyuninBEntry_3_24_eval

def interval_3_24 : NamedVasyuninInterval :=
{
  h := 3
  k := 24
  lower := (14941087/164130000)
  upper := (14973913/164130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_24_interval
}

theorem G3_25_formula : baezDuarteGramEntry 3 25 = vasyuninBEntry 3 25 := vasyuninBEntry_correct_axiom 3 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_25_eval :
    ((((58183431/665690000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 25) ∧
    (vasyuninBEntry 3 25 ≤ (((58316569/665690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_325_formula_bound
  constructor <;> linarith

theorem G3_25_interval :
    ((((58183431/665690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 25) ∧
    (baezDuarteGramEntry 3 25 ≤ (((58316569/665690000) : ℚ) : ℝ)) := by
  rw [G3_25_formula]
  exact vasyuninBEntry_3_25_eval

def interval_3_25 : NamedVasyuninInterval :=
{
  h := 3
  k := 25
  lower := (58183431/665690000)
  upper := (58316569/665690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_25_interval
}

theorem G3_26_formula : baezDuarteGramEntry 3 26 = vasyuninBEntry 3 26 := vasyuninBEntry_correct_axiom 3 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_26_eval :
    ((((6220663/73370000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 26) ∧
    (vasyuninBEntry 3 26 ≤ (((6235337/73370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_326_formula_bound
  constructor <;> linarith

theorem G3_26_interval :
    ((((6220663/73370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 26) ∧
    (baezDuarteGramEntry 3 26 ≤ (((6235337/73370000) : ℚ) : ℝ)) := by
  rw [G3_26_formula]
  exact vasyuninBEntry_3_26_eval

def interval_3_26 : NamedVasyuninInterval :=
{
  h := 3
  k := 26
  lower := (6220663/73370000)
  upper := (6235337/73370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_26_interval
}

theorem G3_27_formula : baezDuarteGramEntry 3 27 = vasyuninBEntry 3 27 := vasyuninBEntry_correct_axiom 3 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_27_eval :
    ((((71344061/859390000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 27) ∧
    (vasyuninBEntry 3 27 ≤ (((71515939/859390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 9 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_27_interval :
    ((((71344061/859390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 27) ∧
    (baezDuarteGramEntry 3 27 ≤ (((71515939/859390000) : ℚ) : ℝ)) := by
  rw [G3_27_formula]
  exact vasyuninBEntry_3_27_eval

def interval_3_27 : NamedVasyuninInterval :=
{
  h := 3
  k := 27
  lower := (71344061/859390000)
  upper := (71515939/859390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_27_interval
}

theorem G3_28_formula : baezDuarteGramEntry 3 28 = vasyuninBEntry 3 28 := vasyuninBEntry_correct_axiom 3 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_28_eval :
    ((((44074949/550510000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 28) ∧
    (vasyuninBEntry 3 28 ≤ (((44185051/550510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_328_formula_bound
  constructor <;> linarith

theorem G3_28_interval :
    ((((44074949/550510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 28) ∧
    (baezDuarteGramEntry 3 28 ≤ (((44185051/550510000) : ℚ) : ℝ)) := by
  rw [G3_28_formula]
  exact vasyuninBEntry_3_28_eval

def interval_3_28 : NamedVasyuninInterval :=
{
  h := 3
  k := 28
  lower := (44074949/550510000)
  upper := (44185051/550510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_28_interval
}

theorem G3_29_formula : baezDuarteGramEntry 3 29 = vasyuninBEntry 3 29 := vasyuninBEntry_correct_axiom 3 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_29_eval :
    ((((11764897/151030000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 29) ∧
    (vasyuninBEntry 3 29 ≤ (((11795103/151030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_329_formula_bound
  constructor <;> linarith

theorem G3_29_interval :
    ((((11764897/151030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 29) ∧
    (baezDuarteGramEntry 3 29 ≤ (((11795103/151030000) : ℚ) : ℝ)) := by
  rw [G3_29_formula]
  exact vasyuninBEntry_3_29_eval

def interval_3_29 : NamedVasyuninInterval :=
{
  h := 3
  k := 29
  lower := (11764897/151030000)
  upper := (11795103/151030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_29_interval
}

theorem G3_30_formula : baezDuarteGramEntry 3 30 = vasyuninBEntry 3 30 := vasyuninBEntry_correct_axiom 3 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_30_eval :
    ((((5373967/70330000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 30) ∧
    (vasyuninBEntry 3 30 ≤ (((5388033/70330000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 10 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_30_interval :
    ((((5373967/70330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 30) ∧
    (baezDuarteGramEntry 3 30 ≤ (((5388033/70330000) : ℚ) : ℝ)) := by
  rw [G3_30_formula]
  exact vasyuninBEntry_3_30_eval

def interval_3_30 : NamedVasyuninInterval :=
{
  h := 3
  k := 30
  lower := (5373967/70330000)
  upper := (5388033/70330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_30_interval
}

theorem G3_31_formula : baezDuarteGramEntry 3 31 = vasyuninBEntry 3 31 := vasyuninBEntry_correct_axiom 3 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_31_eval :
    ((((8773137/118630000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 31) ∧
    (vasyuninBEntry 3 31 ≤ (((8796863/118630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_331_formula_bound
  constructor <;> linarith

theorem G3_31_interval :
    ((((8773137/118630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 31) ∧
    (baezDuarteGramEntry 3 31 ≤ (((8796863/118630000) : ℚ) : ℝ)) := by
  rw [G3_31_formula]
  exact vasyuninBEntry_3_31_eval

def interval_3_31 : NamedVasyuninInterval :=
{
  h := 3
  k := 31
  lower := (8773137/118630000)
  upper := (8796863/118630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_31_interval
}

theorem G3_32_formula : baezDuarteGramEntry 3 32 = vasyuninBEntry 3 32 := vasyuninBEntry_correct_axiom 3 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_32_eval :
    ((((38546561/534390000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 32) ∧
    (vasyuninBEntry 3 32 ≤ (((38653439/534390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_332_formula_bound
  constructor <;> linarith

theorem G3_32_interval :
    ((((38546561/534390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 32) ∧
    (baezDuarteGramEntry 3 32 ≤ (((38653439/534390000) : ℚ) : ℝ)) := by
  rw [G3_32_formula]
  exact vasyuninBEntry_3_32_eval

def interval_3_32 : NamedVasyuninInterval :=
{
  h := 3
  k := 32
  lower := (38546561/534390000)
  upper := (38653439/534390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_32_interval
}

theorem G3_33_formula : baezDuarteGramEntry 3 33 = vasyuninBEntry 3 33 := vasyuninBEntry_correct_axiom 3 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_33_eval :
    ((((31325793/442070000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 33) ∧
    (vasyuninBEntry 3 33 ≤ (((31414207/442070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 11 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_33_interval :
    ((((31325793/442070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 33) ∧
    (baezDuarteGramEntry 3 33 ≤ (((31414207/442070000) : ℚ) : ℝ)) := by
  rw [G3_33_formula]
  exact vasyuninBEntry_3_33_eval

def interval_3_33 : NamedVasyuninInterval :=
{
  h := 3
  k := 33
  lower := (31325793/442070000)
  upper := (31414207/442070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_33_interval
}

theorem G3_34_formula : baezDuarteGramEntry 3 34 = vasyuninBEntry 3 34 := vasyuninBEntry_correct_axiom 3 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_34_eval :
    ((((62189587/904130000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 34) ∧
    (vasyuninBEntry 3 34 ≤ (((62370413/904130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_334_formula_bound
  constructor <;> linarith

theorem G3_34_interval :
    ((((62189587/904130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 34) ∧
    (baezDuarteGramEntry 3 34 ≤ (((62370413/904130000) : ℚ) : ℝ)) := by
  rw [G3_34_formula]
  exact vasyuninBEntry_3_34_eval

def interval_3_34 : NamedVasyuninInterval :=
{
  h := 3
  k := 34
  lower := (62189587/904130000)
  upper := (62370413/904130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_34_interval
}

theorem G3_35_formula : baezDuarteGramEntry 3 35 = vasyuninBEntry 3 35 := vasyuninBEntry_correct_axiom 3 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_35_eval :
    ((((52531859/781410000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 35) ∧
    (vasyuninBEntry 3 35 ≤ (((52688141/781410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_335_formula_bound
  constructor <;> linarith

theorem G3_35_interval :
    ((((52531859/781410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 35) ∧
    (baezDuarteGramEntry 3 35 ≤ (((52688141/781410000) : ℚ) : ℝ)) := by
  rw [G3_35_formula]
  exact vasyuninBEntry_3_35_eval

def interval_3_35 : NamedVasyuninInterval :=
{
  h := 3
  k := 35
  lower := (52531859/781410000)
  upper := (52688141/781410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_35_interval
}

theorem G3_36_formula : baezDuarteGramEntry 3 36 = vasyuninBEntry 3 36 := vasyuninBEntry_correct_axiom 3 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_36_eval :
    ((((47617991/720090000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 36) ∧
    (vasyuninBEntry 3 36 ≤ (((47762009/720090000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 12 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_36_interval :
    ((((47617991/720090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 36) ∧
    (baezDuarteGramEntry 3 36 ≤ (((47762009/720090000) : ℚ) : ℝ)) := by
  rw [G3_36_formula]
  exact vasyuninBEntry_3_36_eval

def interval_3_36 : NamedVasyuninInterval :=
{
  h := 3
  k := 36
  lower := (47617991/720090000)
  upper := (47762009/720090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_36_interval
}

theorem G3_37_formula : baezDuarteGramEntry 3 37 = vasyuninBEntry 3 37 := vasyuninBEntry_correct_axiom 3 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_37_eval :
    ((((3872981/60190000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 37) ∧
    (vasyuninBEntry 3 37 ≤ (((3885019/60190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_337_formula_bound
  constructor <;> linarith

theorem G3_37_interval :
    ((((3872981/60190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 37) ∧
    (baezDuarteGramEntry 3 37 ≤ (((3885019/60190000) : ℚ) : ℝ)) := by
  rw [G3_37_formula]
  exact vasyuninBEntry_3_37_eval

def interval_3_37 : NamedVasyuninInterval :=
{
  h := 3
  k := 37
  lower := (3872981/60190000)
  upper := (3885019/60190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_37_interval
}

theorem G3_38_formula : baezDuarteGramEntry 3 38 = vasyuninBEntry 3 38 := vasyuninBEntry_correct_axiom 3 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_38_eval :
    ((((42292867/671330000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 38) ∧
    (vasyuninBEntry 3 38 ≤ (((42427133/671330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_338_formula_bound
  constructor <;> linarith

theorem G3_38_interval :
    ((((42292867/671330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 38) ∧
    (baezDuarteGramEntry 3 38 ≤ (((42427133/671330000) : ℚ) : ℝ)) := by
  rw [G3_38_formula]
  exact vasyuninBEntry_3_38_eval

def interval_3_38 : NamedVasyuninInterval :=
{
  h := 3
  k := 38
  lower := (42292867/671330000)
  upper := (42427133/671330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_38_interval
}

theorem G3_39_formula : baezDuarteGramEntry 3 39 = vasyuninBEntry 3 39 := vasyuninBEntry_correct_axiom 3 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_39_eval :
    ((((17841241/287590000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 39) ∧
    (vasyuninBEntry 3 39 ≤ (((17898759/287590000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 13 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_39_interval :
    ((((17841241/287590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 39) ∧
    (baezDuarteGramEntry 3 39 ≤ (((17898759/287590000) : ℚ) : ℝ)) := by
  rw [G3_39_formula]
  exact vasyuninBEntry_3_39_eval

def interval_3_39 : NamedVasyuninInterval :=
{
  h := 3
  k := 39
  lower := (17841241/287590000)
  upper := (17898759/287590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_39_interval
}

theorem G3_40_formula : baezDuarteGramEntry 3 40 = vasyuninBEntry 3 40 := vasyuninBEntry_correct_axiom 3 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_40_eval :
    ((((170281/2815000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 40) ∧
    (vasyuninBEntry 3 40 ≤ (((42711/703750) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_340_formula_bound
  constructor <;> linarith

theorem G3_40_interval :
    ((((170281/2815000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 40) ∧
    (baezDuarteGramEntry 3 40 ≤ (((42711/703750) : ℚ) : ℝ)) := by
  rw [G3_40_formula]
  exact vasyuninBEntry_3_40_eval

def interval_3_40 : NamedVasyuninInterval :=
{
  h := 3
  k := 40
  lower := (170281/2815000)
  upper := (42711/703750)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_40_interval
}

theorem G3_41_formula : baezDuarteGramEntry 3 41 = vasyuninBEntry 3 41 := vasyuninBEntry_correct_axiom 3 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_41_eval :
    ((((47599747/802530000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 41) ∧
    (vasyuninBEntry 3 41 ≤ (((47760253/802530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_341_formula_bound
  constructor <;> linarith

theorem G3_41_interval :
    ((((47599747/802530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 41) ∧
    (baezDuarteGramEntry 3 41 ≤ (((47760253/802530000) : ℚ) : ℝ)) := by
  rw [G3_41_formula]
  exact vasyuninBEntry_3_41_eval

def interval_3_41 : NamedVasyuninInterval :=
{
  h := 3
  k := 41
  lower := (47599747/802530000)
  upper := (47760253/802530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_41_interval
}

theorem G3_42_formula : baezDuarteGramEntry 3 42 = vasyuninBEntry 3 42 := vasyuninBEntry_correct_axiom 3 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_42_eval :
    ((((50034417/855830000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 42) ∧
    (vasyuninBEntry 3 42 ≤ (((50205583/855830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 14 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_42_interval :
    ((((50034417/855830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 42) ∧
    (baezDuarteGramEntry 3 42 ≤ (((50205583/855830000) : ℚ) : ℝ)) := by
  rw [G3_42_formula]
  exact vasyuninBEntry_3_42_eval

def interval_3_42 : NamedVasyuninInterval :=
{
  h := 3
  k := 42
  lower := (50034417/855830000)
  upper := (50205583/855830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_42_interval
}

theorem G3_43_formula : baezDuarteGramEntry 3 43 = vasyuninBEntry 3 43 := vasyuninBEntry_correct_axiom 3 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_43_eval :
    ((((17634121/308790000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 43) ∧
    (vasyuninBEntry 3 43 ≤ (((17695879/308790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_343_formula_bound
  constructor <;> linarith

theorem G3_43_interval :
    ((((17634121/308790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 43) ∧
    (baezDuarteGramEntry 3 43 ≤ (((17695879/308790000) : ℚ) : ℝ)) := by
  rw [G3_43_formula]
  exact vasyuninBEntry_3_43_eval

def interval_3_43 : NamedVasyuninInterval :=
{
  h := 3
  k := 43
  lower := (17634121/308790000)
  upper := (17695879/308790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_43_interval
}

theorem G3_44_formula : baezDuarteGramEntry 3 44 = vasyuninBEntry 3 44 := vasyuninBEntry_correct_axiom 3 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_44_eval :
    ((((33989377/606230000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 44) ∧
    (vasyuninBEntry 3 44 ≤ (((34110623/606230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_344_formula_bound
  constructor <;> linarith

theorem G3_44_interval :
    ((((33989377/606230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 44) ∧
    (baezDuarteGramEntry 3 44 ≤ (((34110623/606230000) : ℚ) : ℝ)) := by
  rw [G3_44_formula]
  exact vasyuninBEntry_3_44_eval

def interval_3_44 : NamedVasyuninInterval :=
{
  h := 3
  k := 44
  lower := (33989377/606230000)
  upper := (34110623/606230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_44_interval
}

theorem G3_45_formula : baezDuarteGramEntry 3 45 = vasyuninBEntry 3 45 := vasyuninBEntry_correct_axiom 3 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_45_eval :
    ((((53752817/971830000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 45) ∧
    (vasyuninBEntry 3 45 ≤ (((53947183/971830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 15 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_45_interval :
    ((((53752817/971830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 45) ∧
    (baezDuarteGramEntry 3 45 ≤ (((53947183/971830000) : ℚ) : ℝ)) := by
  rw [G3_45_formula]
  exact vasyuninBEntry_3_45_eval

def interval_3_45 : NamedVasyuninInterval :=
{
  h := 3
  k := 45
  lower := (53752817/971830000)
  upper := (53947183/971830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_45_interval
}

theorem G3_46_formula : baezDuarteGramEntry 3 46 = vasyuninBEntry 3 46 := vasyuninBEntry_correct_axiom 3 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_46_eval :
    ((((21989363/406370000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 46) ∧
    (vasyuninBEntry 3 46 ≤ (((22070637/406370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_346_formula_bound
  constructor <;> linarith

theorem G3_46_interval :
    ((((21989363/406370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 46) ∧
    (baezDuarteGramEntry 3 46 ≤ (((22070637/406370000) : ℚ) : ℝ)) := by
  rw [G3_46_formula]
  exact vasyuninBEntry_3_46_eval

def interval_3_46 : NamedVasyuninInterval :=
{
  h := 3
  k := 46
  lower := (21989363/406370000)
  upper := (22070637/406370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_46_interval
}

theorem G3_47_formula : baezDuarteGramEntry 3 47 = vasyuninBEntry 3 47 := vasyuninBEntry_correct_axiom 3 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_47_eval :
    ((((289331/5440000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 47) ∧
    (vasyuninBEntry 3 47 ≤ (((290419/5440000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_347_formula_bound
  constructor <;> linarith

theorem G3_47_interval :
    ((((289331/5440000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 47) ∧
    (baezDuarteGramEntry 3 47 ≤ (((290419/5440000) : ℚ) : ℝ)) := by
  rw [G3_47_formula]
  exact vasyuninBEntry_3_47_eval

def interval_3_47 : NamedVasyuninInterval :=
{
  h := 3
  k := 47
  lower := (289331/5440000)
  upper := (290419/5440000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_47_interval
}

theorem G3_48_formula : baezDuarteGramEntry 3 48 = vasyuninBEntry 3 48 := vasyuninBEntry_correct_axiom 3 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_48_eval :
    ((((44784709/852910000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 48) ∧
    (vasyuninBEntry 3 48 ≤ (((44955291/852910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 16 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G3_48_interval :
    ((((44784709/852910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 48) ∧
    (baezDuarteGramEntry 3 48 ≤ (((44955291/852910000) : ℚ) : ℝ)) := by
  rw [G3_48_formula]
  exact vasyuninBEntry_3_48_eval

def interval_3_48 : NamedVasyuninInterval :=
{
  h := 3
  k := 48
  lower := (44784709/852910000)
  upper := (44955291/852910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_48_interval
}

theorem G3_49_formula : baezDuarteGramEntry 3 49 = vasyuninBEntry 3 49 := vasyuninBEntry_correct_axiom 3 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_49_eval :
    ((((25181047/489530000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 49) ∧
    (vasyuninBEntry 3 49 ≤ (((25278953/489530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_349_formula_bound
  constructor <;> linarith

theorem G3_49_interval :
    ((((25181047/489530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 49) ∧
    (baezDuarteGramEntry 3 49 ≤ (((25278953/489530000) : ℚ) : ℝ)) := by
  rw [G3_49_formula]
  exact vasyuninBEntry_3_49_eval

def interval_3_49 : NamedVasyuninInterval :=
{
  h := 3
  k := 49
  lower := (25181047/489530000)
  upper := (25278953/489530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_49_interval
}

theorem G3_50_formula : baezDuarteGramEntry 3 50 = vasyuninBEntry 3 50 := vasyuninBEntry_correct_axiom 3 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_3_50_eval :
    ((((4600909/90910000) : ℚ) : ℝ) ≤ vasyuninBEntry 3 50) ∧
    (vasyuninBEntry 3 50 ≤ (((4619091/90910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_350_formula_bound
  constructor <;> linarith

theorem G3_50_interval :
    ((((4600909/90910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 3 50) ∧
    (baezDuarteGramEntry 3 50 ≤ (((4619091/90910000) : ℚ) : ℝ)) := by
  rw [G3_50_formula]
  exact vasyuninBEntry_3_50_eval

def interval_3_50 : NamedVasyuninInterval :=
{
  h := 3
  k := 50
  lower := (4600909/90910000)
  upper := (4619091/90910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G3_50_interval
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

theorem G4_5_formula : baezDuarteGramEntry 4 5 = vasyuninBEntry 4 5 := vasyuninBEntry_correct_axiom 4 5 (by norm_num) (by norm_num)

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

theorem G4_6_formula : baezDuarteGramEntry 4 6 = vasyuninBEntry 4 6 := vasyuninBEntry_correct_axiom 4 6 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_6_eval :
    ((((55097507/249930000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 6) ∧
    (vasyuninBEntry 4 6 ≤ (((55147493/249930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G4_7_formula : baezDuarteGramEntry 4 7 = vasyuninBEntry 4 7 := vasyuninBEntry_correct_axiom 4 7 (by norm_num) (by norm_num)

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

theorem G4_8_formula : baezDuarteGramEntry 4 8 = vasyuninBEntry 4 8 := vasyuninBEntry_correct_axiom 4 8 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_8_eval :
    ((((14052717/72830000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 8) ∧
    (vasyuninBEntry 4 8 ≤ (((14067283/72830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 4 (by norm_num) (by norm_num) (by norm_num)
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

theorem G4_9_formula : baezDuarteGramEntry 4 9 = vasyuninBEntry 4 9 := vasyuninBEntry_correct_axiom 4 9 (by norm_num) (by norm_num)

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

theorem G4_10_formula : baezDuarteGramEntry 4 10 = vasyuninBEntry 4 10 := vasyuninBEntry_correct_axiom 4 10 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_10_eval :
    ((((18243461/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 10) ∧
    (vasyuninBEntry 4 10 ≤ (((18266539/115390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G4_11_formula : baezDuarteGramEntry 4 11 = vasyuninBEntry 4 11 := vasyuninBEntry_correct_axiom 4 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_11_eval :
    ((((4931041/33340000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 11) ∧
    (vasyuninBEntry 4 11 ≤ (((4937709/33340000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_411_formula_bound
  constructor <;> linarith

theorem G4_11_interval :
    ((((4931041/33340000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 11) ∧
    (baezDuarteGramEntry 4 11 ≤ (((4937709/33340000) : ℚ) : ℝ)) := by
  rw [G4_11_formula]
  exact vasyuninBEntry_4_11_eval

def interval_4_11 : NamedVasyuninInterval :=
{
  h := 4
  k := 11
  lower := (4931041/33340000)
  upper := (4937709/33340000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_11_interval
}

theorem G4_12_formula : baezDuarteGramEntry 4 12 = vasyuninBEntry 4 12 := vasyuninBEntry_correct_axiom 4 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_12_eval :
    ((((134556331/936690000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 12) ∧
    (vasyuninBEntry 4 12 ≤ (((134743669/936690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_12_interval :
    ((((134556331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 12) ∧
    (baezDuarteGramEntry 4 12 ≤ (((134743669/936690000) : ℚ) : ℝ)) := by
  rw [G4_12_formula]
  exact vasyuninBEntry_4_12_eval

def interval_4_12 : NamedVasyuninInterval :=
{
  h := 4
  k := 12
  lower := (134556331/936690000)
  upper := (134743669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_12_interval
}

theorem G4_13_formula : baezDuarteGramEntry 4 13 = vasyuninBEntry 4 13 := vasyuninBEntry_correct_axiom 4 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_13_eval :
    ((((4026447/30530000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 13) ∧
    (vasyuninBEntry 4 13 ≤ (((4032553/30530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_413_formula_bound
  constructor <;> linarith

theorem G4_13_interval :
    ((((4026447/30530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 13) ∧
    (baezDuarteGramEntry 4 13 ≤ (((4032553/30530000) : ℚ) : ℝ)) := by
  rw [G4_13_formula]
  exact vasyuninBEntry_4_13_eval

def interval_4_13 : NamedVasyuninInterval :=
{
  h := 4
  k := 13
  lower := (4026447/30530000)
  upper := (4032553/30530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_13_interval
}

theorem G4_14_formula : baezDuarteGramEntry 4 14 = vasyuninBEntry 4 14 := vasyuninBEntry_correct_axiom 4 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_14_eval :
    ((((103337357/826430000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 14) ∧
    (vasyuninBEntry 4 14 ≤ (((103502643/826430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 7 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_14_interval :
    ((((103337357/826430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 14) ∧
    (baezDuarteGramEntry 4 14 ≤ (((103502643/826430000) : ℚ) : ℝ)) := by
  rw [G4_14_formula]
  exact vasyuninBEntry_4_14_eval

def interval_4_14 : NamedVasyuninInterval :=
{
  h := 4
  k := 14
  lower := (103337357/826430000)
  upper := (103502643/826430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_14_interval
}

theorem G4_15_formula : baezDuarteGramEntry 4 15 = vasyuninBEntry 4 15 := vasyuninBEntry_correct_axiom 4 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_15_eval :
    ((((22107413/185870000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 15) ∧
    (vasyuninBEntry 4 15 ≤ (((22144587/185870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_415_formula_bound
  constructor <;> linarith

theorem G4_15_interval :
    ((((22107413/185870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 15) ∧
    (baezDuarteGramEntry 4 15 ≤ (((22144587/185870000) : ℚ) : ℝ)) := by
  rw [G4_15_formula]
  exact vasyuninBEntry_4_15_eval

def interval_4_15 : NamedVasyuninInterval :=
{
  h := 4
  k := 15
  lower := (22107413/185870000)
  upper := (22144587/185870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_15_interval
}

theorem G4_16_formula : baezDuarteGramEntry 4 16 = vasyuninBEntry 4 16 := vasyuninBEntry_correct_axiom 4 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_16_eval :
    ((((37947287/327130000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 16) ∧
    (vasyuninBEntry 4 16 ≤ (((38012713/327130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_16_interval :
    ((((37947287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 16) ∧
    (baezDuarteGramEntry 4 16 ≤ (((38012713/327130000) : ℚ) : ℝ)) := by
  rw [G4_16_formula]
  exact vasyuninBEntry_4_16_eval

def interval_4_16 : NamedVasyuninInterval :=
{
  h := 4
  k := 16
  lower := (37947287/327130000)
  upper := (38012713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_16_interval
}

theorem G4_17_formula : baezDuarteGramEntry 4 17 = vasyuninBEntry 4 17 := vasyuninBEntry_correct_axiom 4 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_17_eval :
    ((((3296469/30310000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 17) ∧
    (vasyuninBEntry 4 17 ≤ (((3302531/30310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_417_formula_bound
  constructor <;> linarith

theorem G4_17_interval :
    ((((3296469/30310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 17) ∧
    (baezDuarteGramEntry 4 17 ≤ (((3302531/30310000) : ℚ) : ℝ)) := by
  rw [G4_17_formula]
  exact vasyuninBEntry_4_17_eval

def interval_4_17 : NamedVasyuninInterval :=
{
  h := 4
  k := 17
  lower := (3296469/30310000)
  upper := (3302531/30310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_17_interval
}

theorem G4_18_formula : baezDuarteGramEntry 4 18 = vasyuninBEntry 4 18 := vasyuninBEntry_correct_axiom 4 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_18_eval :
    ((((52819343/506570000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 18) ∧
    (vasyuninBEntry 4 18 ≤ (((52920657/506570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 9 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_18_interval :
    ((((52819343/506570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 18) ∧
    (baezDuarteGramEntry 4 18 ≤ (((52920657/506570000) : ℚ) : ℝ)) := by
  rw [G4_18_formula]
  exact vasyuninBEntry_4_18_eval

def interval_4_18 : NamedVasyuninInterval :=
{
  h := 4
  k := 18
  lower := (52819343/506570000)
  upper := (52920657/506570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_18_interval
}

theorem G4_19_formula : baezDuarteGramEntry 4 19 = vasyuninBEntry 4 19 := vasyuninBEntry_correct_axiom 4 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_19_eval :
    ((((13139383/131170000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 19) ∧
    (vasyuninBEntry 4 19 ≤ (((13165617/131170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_419_formula_bound
  constructor <;> linarith

theorem G4_19_interval :
    ((((13139383/131170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 19) ∧
    (baezDuarteGramEntry 4 19 ≤ (((13165617/131170000) : ℚ) : ℝ)) := by
  rw [G4_19_formula]
  exact vasyuninBEntry_4_19_eval

def interval_4_19 : NamedVasyuninInterval :=
{
  h := 4
  k := 19
  lower := (13139383/131170000)
  upper := (13165617/131170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_19_interval
}

theorem G4_20_formula : baezDuarteGramEntry 4 20 = vasyuninBEntry 4 20 := vasyuninBEntry_correct_axiom 4 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_20_eval :
    ((((32112239/327610000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 20) ∧
    (vasyuninBEntry 4 20 ≤ (((32177761/327610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_20_interval :
    ((((32112239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 20) ∧
    (baezDuarteGramEntry 4 20 ≤ (((32177761/327610000) : ℚ) : ℝ)) := by
  rw [G4_20_formula]
  exact vasyuninBEntry_4_20_eval

def interval_4_20 : NamedVasyuninInterval :=
{
  h := 4
  k := 20
  lower := (32112239/327610000)
  upper := (32177761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_20_interval
}

theorem G4_21_formula : baezDuarteGramEntry 4 21 = vasyuninBEntry 4 21 := vasyuninBEntry_correct_axiom 4 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_21_eval :
    ((((21699187/233130000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 21) ∧
    (vasyuninBEntry 4 21 ≤ (((21745813/233130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_421_formula_bound
  constructor <;> linarith

theorem G4_21_interval :
    ((((21699187/233130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 21) ∧
    (baezDuarteGramEntry 4 21 ≤ (((21745813/233130000) : ℚ) : ℝ)) := by
  rw [G4_21_formula]
  exact vasyuninBEntry_4_21_eval

def interval_4_21 : NamedVasyuninInterval :=
{
  h := 4
  k := 21
  lower := (21699187/233130000)
  upper := (21745813/233130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_21_interval
}

theorem G4_22_formula : baezDuarteGramEntry 4 22 = vasyuninBEntry 4 22 := vasyuninBEntry_correct_axiom 4 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_22_eval :
    ((((73158607/813930000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 22) ∧
    (vasyuninBEntry 4 22 ≤ (((73321393/813930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 11 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_22_interval :
    ((((73158607/813930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 22) ∧
    (baezDuarteGramEntry 4 22 ≤ (((73321393/813930000) : ℚ) : ℝ)) := by
  rw [G4_22_formula]
  exact vasyuninBEntry_4_22_eval

def interval_4_22 : NamedVasyuninInterval :=
{
  h := 4
  k := 22
  lower := (73158607/813930000)
  upper := (73321393/813930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_22_interval
}

theorem G4_23_formula : baezDuarteGramEntry 4 23 = vasyuninBEntry 4 23 := vasyuninBEntry_correct_axiom 4 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_23_eval :
    ((((1713229/19710000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 23) ∧
    (vasyuninBEntry 4 23 ≤ (((1717171/19710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_423_formula_bound
  constructor <;> linarith

theorem G4_23_interval :
    ((((1713229/19710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 23) ∧
    (baezDuarteGramEntry 4 23 ≤ (((1717171/19710000) : ℚ) : ℝ)) := by
  rw [G4_23_formula]
  exact vasyuninBEntry_4_23_eval

def interval_4_23 : NamedVasyuninInterval :=
{
  h := 4
  k := 23
  lower := (1713229/19710000)
  upper := (1717171/19710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_23_interval
}

theorem G4_24_formula : baezDuarteGramEntry 4 24 = vasyuninBEntry 4 24 := vasyuninBEntry_correct_axiom 4 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_24_eval :
    ((((71156557/834430000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 24) ∧
    (vasyuninBEntry 4 24 ≤ (((71323443/834430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 6 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_24_interval :
    ((((71156557/834430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 24) ∧
    (baezDuarteGramEntry 4 24 ≤ (((71323443/834430000) : ℚ) : ℝ)) := by
  rw [G4_24_formula]
  exact vasyuninBEntry_4_24_eval

def interval_4_24 : NamedVasyuninInterval :=
{
  h := 4
  k := 24
  lower := (71156557/834430000)
  upper := (71323443/834430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_24_interval
}

theorem G4_25_formula : baezDuarteGramEntry 4 25 = vasyuninBEntry 4 25 := vasyuninBEntry_correct_axiom 4 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_25_eval :
    ((((11106401/135990000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 25) ∧
    (vasyuninBEntry 4 25 ≤ (((11133599/135990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_425_formula_bound
  constructor <;> linarith

theorem G4_25_interval :
    ((((11106401/135990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 25) ∧
    (baezDuarteGramEntry 4 25 ≤ (((11133599/135990000) : ℚ) : ℝ)) := by
  rw [G4_25_formula]
  exact vasyuninBEntry_4_25_eval

def interval_4_25 : NamedVasyuninInterval :=
{
  h := 4
  k := 25
  lower := (11106401/135990000)
  upper := (11133599/135990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_25_interval
}

theorem G4_26_formula : baezDuarteGramEntry 4 26 = vasyuninBEntry 4 26 := vasyuninBEntry_correct_axiom 4 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_26_eval :
    ((((61252729/772710000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 26) ∧
    (vasyuninBEntry 4 26 ≤ (((61407271/772710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 13 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_26_interval :
    ((((61252729/772710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 26) ∧
    (baezDuarteGramEntry 4 26 ≤ (((61407271/772710000) : ℚ) : ℝ)) := by
  rw [G4_26_formula]
  exact vasyuninBEntry_4_26_eval

def interval_4_26 : NamedVasyuninInterval :=
{
  h := 4
  k := 26
  lower := (61252729/772710000)
  upper := (61407271/772710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_26_interval
}

theorem G4_27_formula : baezDuarteGramEntry 4 27 = vasyuninBEntry 4 27 := vasyuninBEntry_correct_axiom 4 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_27_eval :
    ((((16558501/214990000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 27) ∧
    (vasyuninBEntry 4 27 ≤ (((16601499/214990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_427_formula_bound
  constructor <;> linarith

theorem G4_27_interval :
    ((((16558501/214990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 27) ∧
    (baezDuarteGramEntry 4 27 ≤ (((16601499/214990000) : ℚ) : ℝ)) := by
  rw [G4_27_formula]
  exact vasyuninBEntry_4_27_eval

def interval_4_27 : NamedVasyuninInterval :=
{
  h := 4
  k := 27
  lower := (16558501/214990000)
  upper := (16601499/214990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_27_interval
}

theorem G4_28_formula : baezDuarteGramEntry 4 28 = vasyuninBEntry 4 28 := vasyuninBEntry_correct_axiom 4 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_28_eval :
    ((((38818731/512690000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 28) ∧
    (vasyuninBEntry 4 28 ≤ (((38921269/512690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 7 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_28_interval :
    ((((38818731/512690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 28) ∧
    (baezDuarteGramEntry 4 28 ≤ (((38921269/512690000) : ℚ) : ℝ)) := by
  rw [G4_28_formula]
  exact vasyuninBEntry_4_28_eval

def interval_4_28 : NamedVasyuninInterval :=
{
  h := 4
  k := 28
  lower := (38818731/512690000)
  upper := (38921269/512690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_28_interval
}

theorem G4_29_formula : baezDuarteGramEntry 4 29 = vasyuninBEntry 4 29 := vasyuninBEntry_correct_axiom 4 29 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_29_eval :
    ((((686559/9410000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 29) ∧
    (vasyuninBEntry 4 29 ≤ (((688441/9410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_429_formula_bound
  constructor <;> linarith

theorem G4_29_interval :
    ((((686559/9410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 29) ∧
    (baezDuarteGramEntry 4 29 ≤ (((688441/9410000) : ℚ) : ℝ)) := by
  rw [G4_29_formula]
  exact vasyuninBEntry_4_29_eval

def interval_4_29 : NamedVasyuninInterval :=
{
  h := 4
  k := 29
  lower := (686559/9410000)
  upper := (688441/9410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_29_interval
}

theorem G4_30_formula : baezDuarteGramEntry 4 30 = vasyuninBEntry 4 30 := vasyuninBEntry_correct_axiom 4 30 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_30_eval :
    ((((4200341/59090000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 30) ∧
    (vasyuninBEntry 4 30 ≤ (((4212159/59090000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 15 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_30_interval :
    ((((4200341/59090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 30) ∧
    (baezDuarteGramEntry 4 30 ≤ (((4212159/59090000) : ℚ) : ℝ)) := by
  rw [G4_30_formula]
  exact vasyuninBEntry_4_30_eval

def interval_4_30 : NamedVasyuninInterval :=
{
  h := 4
  k := 30
  lower := (4200341/59090000)
  upper := (4212159/59090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_30_interval
}

theorem G4_31_formula : baezDuarteGramEntry 4 31 = vasyuninBEntry 4 31 := vasyuninBEntry_correct_axiom 4 31 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_31_eval :
    ((((57127577/824230000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 31) ∧
    (vasyuninBEntry 4 31 ≤ (((57292423/824230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_431_formula_bound
  constructor <;> linarith

theorem G4_31_interval :
    ((((57127577/824230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 31) ∧
    (baezDuarteGramEntry 4 31 ≤ (((57292423/824230000) : ℚ) : ℝ)) := by
  rw [G4_31_formula]
  exact vasyuninBEntry_4_31_eval

def interval_4_31 : NamedVasyuninInterval :=
{
  h := 4
  k := 31
  lower := (57127577/824230000)
  upper := (57292423/824230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_31_interval
}

theorem G4_32_formula : baezDuarteGramEntry 4 32 = vasyuninBEntry 4 32 := vasyuninBEntry_correct_axiom 4 32 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_32_eval :
    ((((233369/3419375) : ℚ) : ℝ) ≤ vasyuninBEntry 4 32) ∧
    (vasyuninBEntry 4 32 ≤ (((1872423/27355000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 8 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_32_interval :
    ((((233369/3419375) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 32) ∧
    (baezDuarteGramEntry 4 32 ≤ (((1872423/27355000) : ℚ) : ℝ)) := by
  rw [G4_32_formula]
  exact vasyuninBEntry_4_32_eval

def interval_4_32 : NamedVasyuninInterval :=
{
  h := 4
  k := 32
  lower := (233369/3419375)
  upper := (1872423/27355000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_32_interval
}

theorem G4_33_formula : baezDuarteGramEntry 4 33 = vasyuninBEntry 4 33 := vasyuninBEntry_correct_axiom 4 33 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_33_eval :
    ((((8676867/131330000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 33) ∧
    (vasyuninBEntry 4 33 ≤ (((8703133/131330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_433_formula_bound
  constructor <;> linarith

theorem G4_33_interval :
    ((((8676867/131330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 33) ∧
    (baezDuarteGramEntry 4 33 ≤ (((8703133/131330000) : ℚ) : ℝ)) := by
  rw [G4_33_formula]
  exact vasyuninBEntry_4_33_eval

def interval_4_33 : NamedVasyuninInterval :=
{
  h := 4
  k := 33
  lower := (8676867/131330000)
  upper := (8703133/131330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_33_interval
}

theorem G4_34_formula : baezDuarteGramEntry 4 34 = vasyuninBEntry 4 34 := vasyuninBEntry_correct_axiom 4 34 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_34_eval :
    ((((17073553/264470000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 34) ∧
    (vasyuninBEntry 4 34 ≤ (((17126447/264470000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 17 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_34_interval :
    ((((17073553/264470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 34) ∧
    (baezDuarteGramEntry 4 34 ≤ (((17126447/264470000) : ℚ) : ℝ)) := by
  rw [G4_34_formula]
  exact vasyuninBEntry_4_34_eval

def interval_4_34 : NamedVasyuninInterval :=
{
  h := 4
  k := 34
  lower := (17073553/264470000)
  upper := (17126447/264470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_34_interval
}

theorem G4_35_formula : baezDuarteGramEntry 4 35 = vasyuninBEntry 4 35 := vasyuninBEntry_correct_axiom 4 35 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_35_eval :
    ((((2750143/43570000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 35) ∧
    (vasyuninBEntry 4 35 ≤ (((2758857/43570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_435_formula_bound
  constructor <;> linarith

theorem G4_35_interval :
    ((((2750143/43570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 35) ∧
    (baezDuarteGramEntry 4 35 ≤ (((2758857/43570000) : ℚ) : ℝ)) := by
  rw [G4_35_formula]
  exact vasyuninBEntry_4_35_eval

def interval_4_35 : NamedVasyuninInterval :=
{
  h := 4
  k := 35
  lower := (2750143/43570000)
  upper := (2758857/43570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_35_interval
}

theorem G4_36_formula : baezDuarteGramEntry 4 36 = vasyuninBEntry 4 36 := vasyuninBEntry_correct_axiom 4 36 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_36_eval :
    ((((20387243/327570000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 36) ∧
    (vasyuninBEntry 4 36 ≤ (((20452757/327570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 9 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_36_interval :
    ((((20387243/327570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 36) ∧
    (baezDuarteGramEntry 4 36 ≤ (((20452757/327570000) : ℚ) : ℝ)) := by
  rw [G4_36_formula]
  exact vasyuninBEntry_4_36_eval

def interval_4_36 : NamedVasyuninInterval :=
{
  h := 4
  k := 36
  lower := (20387243/327570000)
  upper := (20452757/327570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_36_interval
}

theorem G4_37_formula : baezDuarteGramEntry 4 37 = vasyuninBEntry 4 37 := vasyuninBEntry_correct_axiom 4 37 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_37_eval :
    ((((1817931/30065000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 37) ∧
    (vasyuninBEntry 4 37 ≤ (((227993/3758125) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_437_formula_bound
  constructor <;> linarith

theorem G4_37_interval :
    ((((1817931/30065000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 37) ∧
    (baezDuarteGramEntry 4 37 ≤ (((227993/3758125) : ℚ) : ℝ)) := by
  rw [G4_37_formula]
  exact vasyuninBEntry_4_37_eval

def interval_4_37 : NamedVasyuninInterval :=
{
  h := 4
  k := 37
  lower := (1817931/30065000)
  upper := (227993/3758125)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_37_interval
}

theorem G4_38_formula : baezDuarteGramEntry 4 38 = vasyuninBEntry 4 38 := vasyuninBEntry_correct_axiom 4 38 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_38_eval :
    ((((43945793/742070000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 38) ∧
    (vasyuninBEntry 4 38 ≤ (((44094207/742070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 19 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_38_interval :
    ((((43945793/742070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 38) ∧
    (baezDuarteGramEntry 4 38 ≤ (((44094207/742070000) : ℚ) : ℝ)) := by
  rw [G4_38_formula]
  exact vasyuninBEntry_4_38_eval

def interval_4_38 : NamedVasyuninInterval :=
{
  h := 4
  k := 38
  lower := (43945793/742070000)
  upper := (44094207/742070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_38_interval
}

theorem G4_39_formula : baezDuarteGramEntry 4 39 = vasyuninBEntry 4 39 := vasyuninBEntry_correct_axiom 4 39 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_39_eval :
    ((((2680381/46190000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 39) ∧
    (vasyuninBEntry 4 39 ≤ (((2689619/46190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_439_formula_bound
  constructor <;> linarith

theorem G4_39_interval :
    ((((2680381/46190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 39) ∧
    (baezDuarteGramEntry 4 39 ≤ (((2689619/46190000) : ℚ) : ℝ)) := by
  rw [G4_39_formula]
  exact vasyuninBEntry_4_39_eval

def interval_4_39 : NamedVasyuninInterval :=
{
  h := 4
  k := 39
  lower := (2680381/46190000)
  upper := (2689619/46190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_39_interval
}

theorem G4_40_formula : baezDuarteGramEntry 4 40 = vasyuninBEntry 4 40 := vasyuninBEntry_correct_axiom 4 40 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_40_eval :
    ((((20339493/355070000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 40) ∧
    (vasyuninBEntry 4 40 ≤ (((20410507/355070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 10 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_40_interval :
    ((((20339493/355070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 40) ∧
    (baezDuarteGramEntry 4 40 ≤ (((20410507/355070000) : ℚ) : ℝ)) := by
  rw [G4_40_formula]
  exact vasyuninBEntry_4_40_eval

def interval_4_40 : NamedVasyuninInterval :=
{
  h := 4
  k := 40
  lower := (20339493/355070000)
  upper := (20410507/355070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_40_interval
}

theorem G4_41_formula : baezDuarteGramEntry 4 41 = vasyuninBEntry 4 41 := vasyuninBEntry_correct_axiom 4 41 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_41_eval :
    ((((17598469/315310000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 41) ∧
    (vasyuninBEntry 4 41 ≤ (((17661531/315310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_441_formula_bound
  constructor <;> linarith

theorem G4_41_interval :
    ((((17598469/315310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 41) ∧
    (baezDuarteGramEntry 4 41 ≤ (((17661531/315310000) : ℚ) : ℝ)) := by
  rw [G4_41_formula]
  exact vasyuninBEntry_4_41_eval

def interval_4_41 : NamedVasyuninInterval :=
{
  h := 4
  k := 41
  lower := (17598469/315310000)
  upper := (17661531/315310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_41_interval
}

theorem G4_42_formula : baezDuarteGramEntry 4 42 = vasyuninBEntry 4 42 := vasyuninBEntry_correct_axiom 4 42 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_42_eval :
    ((((18191783/332170000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 42) ∧
    (vasyuninBEntry 4 42 ≤ (((18258217/332170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 21 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_42_interval :
    ((((18191783/332170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 42) ∧
    (baezDuarteGramEntry 4 42 ≤ (((18258217/332170000) : ℚ) : ℝ)) := by
  rw [G4_42_formula]
  exact vasyuninBEntry_4_42_eval

def interval_4_42 : NamedVasyuninInterval :=
{
  h := 4
  k := 42
  lower := (18191783/332170000)
  upper := (18258217/332170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_42_interval
}

theorem G4_43_formula : baezDuarteGramEntry 4 43 = vasyuninBEntry 4 43 := vasyuninBEntry_correct_axiom 4 43 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_43_eval :
    ((((41882097/779030000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 43) ∧
    (vasyuninBEntry 4 43 ≤ (((42037903/779030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_443_formula_bound
  constructor <;> linarith

theorem G4_43_interval :
    ((((41882097/779030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 43) ∧
    (baezDuarteGramEntry 4 43 ≤ (((42037903/779030000) : ℚ) : ℝ)) := by
  rw [G4_43_formula]
  exact vasyuninBEntry_4_43_eval

def interval_4_43 : NamedVasyuninInterval :=
{
  h := 4
  k := 43
  lower := (41882097/779030000)
  upper := (42037903/779030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_43_interval
}

theorem G4_44_formula : baezDuarteGramEntry 4 44 = vasyuninBEntry 4 44 := vasyuninBEntry_correct_axiom 4 44 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_44_eval :
    ((((37459483/705170000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 44) ∧
    (vasyuninBEntry 4 44 ≤ (((37600517/705170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 11 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_44_interval :
    ((((37459483/705170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 44) ∧
    (baezDuarteGramEntry 4 44 ≤ (((37600517/705170000) : ℚ) : ℝ)) := by
  rw [G4_44_formula]
  exact vasyuninBEntry_4_44_eval

def interval_4_44 : NamedVasyuninInterval :=
{
  h := 4
  k := 44
  lower := (37459483/705170000)
  upper := (37600517/705170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_44_interval
}

theorem G4_45_formula : baezDuarteGramEntry 4 45 = vasyuninBEntry 4 45 := vasyuninBEntry_correct_axiom 4 45 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_45_eval :
    ((((21338869/411310000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 45) ∧
    (vasyuninBEntry 4 45 ≤ (((21421131/411310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_445_formula_bound
  constructor <;> linarith

theorem G4_45_interval :
    ((((21338869/411310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 45) ∧
    (baezDuarteGramEntry 4 45 ≤ (((21421131/411310000) : ℚ) : ℝ)) := by
  rw [G4_45_formula]
  exact vasyuninBEntry_4_45_eval

def interval_4_45 : NamedVasyuninInterval :=
{
  h := 4
  k := 45
  lower := (21338869/411310000)
  upper := (21421131/411310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_45_interval
}

theorem G4_46_formula : baezDuarteGramEntry 4 46 = vasyuninBEntry 4 46 := vasyuninBEntry_correct_axiom 4 46 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_46_eval :
    ((((50431091/989090000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 46) ∧
    (vasyuninBEntry 4 46 ≤ (((50628909/989090000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 23 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_46_interval :
    ((((50431091/989090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 46) ∧
    (baezDuarteGramEntry 4 46 ≤ (((50628909/989090000) : ℚ) : ℝ)) := by
  rw [G4_46_formula]
  exact vasyuninBEntry_4_46_eval

def interval_4_46 : NamedVasyuninInterval :=
{
  h := 4
  k := 46
  lower := (50431091/989090000)
  upper := (50628909/989090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_46_interval
}

theorem G4_47_formula : baezDuarteGramEntry 4 47 = vasyuninBEntry 4 47 := vasyuninBEntry_correct_axiom 4 47 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_47_eval :
    ((((5113/102000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 47) ∧
    (vasyuninBEntry 4 47 ≤ (((25667/510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_447_formula_bound
  constructor <;> linarith

theorem G4_47_interval :
    ((((5113/102000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 47) ∧
    (baezDuarteGramEntry 4 47 ≤ (((25667/510000) : ℚ) : ℝ)) := by
  rw [G4_47_formula]
  exact vasyuninBEntry_4_47_eval

def interval_4_47 : NamedVasyuninInterval :=
{
  h := 4
  k := 47
  lower := (5113/102000)
  upper := (25667/510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_47_interval
}

theorem G4_48_formula : baezDuarteGramEntry 4 48 = vasyuninBEntry 4 48 := vasyuninBEntry_correct_axiom 4 48 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_48_eval :
    ((((11898497/240030000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 48) ∧
    (vasyuninBEntry 4 48 ≤ (((11946503/240030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 12 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G4_48_interval :
    ((((11898497/240030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 48) ∧
    (baezDuarteGramEntry 4 48 ≤ (((11946503/240030000) : ℚ) : ℝ)) := by
  rw [G4_48_formula]
  exact vasyuninBEntry_4_48_eval

def interval_4_48 : NamedVasyuninInterval :=
{
  h := 4
  k := 48
  lower := (11898497/240030000)
  upper := (11946503/240030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_48_interval
}

theorem G4_49_formula : baezDuarteGramEntry 4 49 = vasyuninBEntry 4 49 := vasyuninBEntry_correct_axiom 4 49 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_49_eval :
    ((((36714313/756870000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 49) ∧
    (vasyuninBEntry 4 49 ≤ (((36865687/756870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_449_formula_bound
  constructor <;> linarith

theorem G4_49_interval :
    ((((36714313/756870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 49) ∧
    (baezDuarteGramEntry 4 49 ≤ (((36865687/756870000) : ℚ) : ℝ)) := by
  rw [G4_49_formula]
  exact vasyuninBEntry_4_49_eval

def interval_4_49 : NamedVasyuninInterval :=
{
  h := 4
  k := 49
  lower := (36714313/756870000)
  upper := (36865687/756870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_49_interval
}

theorem G4_50_formula : baezDuarteGramEntry 4 50 = vasyuninBEntry 4 50 := vasyuninBEntry_correct_axiom 4 50 (by norm_num) (by norm_num)

theorem vasyuninBEntry_4_50_eval :
    ((((21215557/444430000) : ℚ) : ℝ) ≤ vasyuninBEntry 4 50) ∧
    (vasyuninBEntry 4 50 ≤ (((21304443/444430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 25 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G4_50_interval :
    ((((21215557/444430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 4 50) ∧
    (baezDuarteGramEntry 4 50 ≤ (((21304443/444430000) : ℚ) : ℝ)) := by
  rw [G4_50_formula]
  exact vasyuninBEntry_4_50_eval

def interval_4_50 : NamedVasyuninInterval :=
{
  h := 4
  k := 50
  lower := (21215557/444430000)
  upper := (21304443/444430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G4_50_interval
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

theorem G5_6_formula : baezDuarteGramEntry 5 6 = vasyuninBEntry 5 6 := vasyuninBEntry_correct_axiom 5 6 (by norm_num) (by norm_num)

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

theorem G5_7_formula : baezDuarteGramEntry 5 7 = vasyuninBEntry 5 7 := vasyuninBEntry_correct_axiom 5 7 (by norm_num) (by norm_num)

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

theorem G5_8_formula : baezDuarteGramEntry 5 8 = vasyuninBEntry 5 8 := vasyuninBEntry_correct_axiom 5 8 (by norm_num) (by norm_num)

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

theorem G5_9_formula : baezDuarteGramEntry 5 9 = vasyuninBEntry 5 9 := vasyuninBEntry_correct_axiom 5 9 (by norm_num) (by norm_num)

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

theorem G5_10_formula : baezDuarteGramEntry 5 10 = vasyuninBEntry 5 10 := vasyuninBEntry_correct_axiom 5 10 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_10_eval :
    ((((50922007/329930000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 10) ∧
    (vasyuninBEntry 5 10 ≤ (((50987993/329930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 5 (by norm_num) (by norm_num) (by norm_num)
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

theorem G5_11_formula : baezDuarteGramEntry 5 11 = vasyuninBEntry 5 11 := vasyuninBEntry_correct_axiom 5 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_11_eval :
    ((((47031043/339570000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 11) ∧
    (vasyuninBEntry 5 11 ≤ (((47098957/339570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_511_formula_bound
  constructor <;> linarith

theorem G5_11_interval :
    ((((47031043/339570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 11) ∧
    (baezDuarteGramEntry 5 11 ≤ (((47098957/339570000) : ℚ) : ℝ)) := by
  rw [G5_11_formula]
  exact vasyuninBEntry_5_11_eval

def interval_5_11 : NamedVasyuninInterval :=
{
  h := 5
  k := 11
  lower := (47031043/339570000)
  upper := (47098957/339570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_11_interval
}

theorem G5_12_formula : baezDuarteGramEntry 5 12 = vasyuninBEntry 5 12 := vasyuninBEntry_correct_axiom 5 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_12_eval :
    ((((40823471/315290000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 12) ∧
    (vasyuninBEntry 5 12 ≤ (((40886529/315290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_512_formula_bound
  constructor <;> linarith

theorem G5_12_interval :
    ((((40823471/315290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 12) ∧
    (baezDuarteGramEntry 5 12 ≤ (((40886529/315290000) : ℚ) : ℝ)) := by
  rw [G5_12_formula]
  exact vasyuninBEntry_5_12_eval

def interval_5_12 : NamedVasyuninInterval :=
{
  h := 5
  k := 12
  lower := (40823471/315290000)
  upper := (40886529/315290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_12_interval
}

theorem G5_13_formula : baezDuarteGramEntry 5 13 = vasyuninBEntry 5 13 := vasyuninBEntry_correct_axiom 5 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_13_eval :
    ((((114946181/938190000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 13) ∧
    (vasyuninBEntry 5 13 ≤ (((115133819/938190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_513_formula_bound
  constructor <;> linarith

theorem G5_13_interval :
    ((((114946181/938190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 13) ∧
    (baezDuarteGramEntry 5 13 ≤ (((115133819/938190000) : ℚ) : ℝ)) := by
  rw [G5_13_formula]
  exact vasyuninBEntry_5_13_eval

def interval_5_13 : NamedVasyuninInterval :=
{
  h := 5
  k := 13
  lower := (114946181/938190000)
  upper := (115133819/938190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_13_interval
}

theorem G5_14_formula : baezDuarteGramEntry 5 14 = vasyuninBEntry 5 14 := vasyuninBEntry_correct_axiom 5 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_14_eval :
    ((((3848713/32870000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 14) ∧
    (vasyuninBEntry 5 14 ≤ (((3855287/32870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_514_formula_bound
  constructor <;> linarith

theorem G5_14_interval :
    ((((3848713/32870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 14) ∧
    (baezDuarteGramEntry 5 14 ≤ (((3855287/32870000) : ℚ) : ℝ)) := by
  rw [G5_14_formula]
  exact vasyuninBEntry_5_14_eval

def interval_5_14 : NamedVasyuninInterval :=
{
  h := 5
  k := 14
  lower := (3848713/32870000)
  upper := (3855287/32870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_14_interval
}

theorem G5_15_formula : baezDuarteGramEntry 5 15 = vasyuninBEntry 5 15 := vasyuninBEntry_correct_axiom 5 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_15_eval :
    ((((107626331/936690000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 15) ∧
    (vasyuninBEntry 5 15 ≤ (((107813669/936690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_15_interval :
    ((((107626331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 15) ∧
    (baezDuarteGramEntry 5 15 ≤ (((107813669/936690000) : ℚ) : ℝ)) := by
  rw [G5_15_formula]
  exact vasyuninBEntry_5_15_eval

def interval_5_15 : NamedVasyuninInterval :=
{
  h := 5
  k := 15
  lower := (107626331/936690000)
  upper := (107813669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_15_interval
}

theorem G5_16_formula : baezDuarteGramEntry 5 16 = vasyuninBEntry 5 16 := vasyuninBEntry_correct_axiom 5 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_16_eval :
    ((((19049673/178270000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 16) ∧
    (vasyuninBEntry 5 16 ≤ (((19085327/178270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_516_formula_bound
  constructor <;> linarith

theorem G5_16_interval :
    ((((19049673/178270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 16) ∧
    (baezDuarteGramEntry 5 16 ≤ (((19085327/178270000) : ℚ) : ℝ)) := by
  rw [G5_16_formula]
  exact vasyuninBEntry_5_16_eval

def interval_5_16 : NamedVasyuninInterval :=
{
  h := 5
  k := 16
  lower := (19049673/178270000)
  upper := (19085327/178270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_16_interval
}

theorem G5_17_formula : baezDuarteGramEntry 5 17 = vasyuninBEntry 5 17 := vasyuninBEntry_correct_axiom 5 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_17_eval :
    ((((43667113/428870000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 17) ∧
    (vasyuninBEntry 5 17 ≤ (((43752887/428870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_517_formula_bound
  constructor <;> linarith

theorem G5_17_interval :
    ((((43667113/428870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 17) ∧
    (baezDuarteGramEntry 5 17 ≤ (((43752887/428870000) : ℚ) : ℝ)) := by
  rw [G5_17_formula]
  exact vasyuninBEntry_5_17_eval

def interval_5_17 : NamedVasyuninInterval :=
{
  h := 5
  k := 17
  lower := (43667113/428870000)
  upper := (43752887/428870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_17_interval
}

theorem G5_18_formula : baezDuarteGramEntry 5 18 = vasyuninBEntry 5 18 := vasyuninBEntry_correct_axiom 5 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_18_eval :
    ((((24899519/254810000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 18) ∧
    (vasyuninBEntry 5 18 ≤ (((24950481/254810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_518_formula_bound
  constructor <;> linarith

theorem G5_18_interval :
    ((((24899519/254810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 18) ∧
    (baezDuarteGramEntry 5 18 ≤ (((24950481/254810000) : ℚ) : ℝ)) := by
  rw [G5_18_formula]
  exact vasyuninBEntry_5_18_eval

def interval_5_18 : NamedVasyuninInterval :=
{
  h := 5
  k := 18
  lower := (24899519/254810000)
  upper := (24950481/254810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_18_interval
}

theorem G5_19_formula : baezDuarteGramEntry 5 19 = vasyuninBEntry 5 19 := vasyuninBEntry_correct_axiom 5 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_19_eval :
    ((((37759987/400130000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 19) ∧
    (vasyuninBEntry 5 19 ≤ (((37840013/400130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_519_formula_bound
  constructor <;> linarith

theorem G5_19_interval :
    ((((37759987/400130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 19) ∧
    (baezDuarteGramEntry 5 19 ≤ (((37840013/400130000) : ℚ) : ℝ)) := by
  rw [G5_19_formula]
  exact vasyuninBEntry_5_19_eval

def interval_5_19 : NamedVasyuninInterval :=
{
  h := 5
  k := 19
  lower := (37759987/400130000)
  upper := (37840013/400130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_19_interval
}

theorem G5_20_formula : baezDuarteGramEntry 5 20 = vasyuninBEntry 5 20 := vasyuninBEntry_correct_axiom 5 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_20_eval :
    ((((21841459/235410000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 20) ∧
    (vasyuninBEntry 5 20 ≤ (((21888541/235410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 4 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_20_interval :
    ((((21841459/235410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 20) ∧
    (baezDuarteGramEntry 5 20 ≤ (((21888541/235410000) : ℚ) : ℝ)) := by
  rw [G5_20_formula]
  exact vasyuninBEntry_5_20_eval

def interval_5_20 : NamedVasyuninInterval :=
{
  h := 5
  k := 20
  lower := (21841459/235410000)
  upper := (21888541/235410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_20_interval
}

theorem G5_21_formula : baezDuarteGramEntry 5 21 = vasyuninBEntry 5 21 := vasyuninBEntry_correct_axiom 5 21 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_21_eval :
    ((((95329/1085000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 21) ∧
    (vasyuninBEntry 5 21 ≤ (((47773/542500) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_521_formula_bound
  constructor <;> linarith

theorem G5_21_interval :
    ((((95329/1085000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 21) ∧
    (baezDuarteGramEntry 5 21 ≤ (((47773/542500) : ℚ) : ℝ)) := by
  rw [G5_21_formula]
  exact vasyuninBEntry_5_21_eval

def interval_5_21 : NamedVasyuninInterval :=
{
  h := 5
  k := 21
  lower := (95329/1085000)
  upper := (47773/542500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_21_interval
}

theorem G5_22_formula : baezDuarteGramEntry 5 22 = vasyuninBEntry 5 22 := vasyuninBEntry_correct_axiom 5 22 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_22_eval :
    ((((18870197/223030000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 22) ∧
    (vasyuninBEntry 5 22 ≤ (((18914803/223030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_522_formula_bound
  constructor <;> linarith

theorem G5_22_interval :
    ((((18870197/223030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 22) ∧
    (baezDuarteGramEntry 5 22 ≤ (((18914803/223030000) : ℚ) : ℝ)) := by
  rw [G5_22_formula]
  exact vasyuninBEntry_5_22_eval

def interval_5_22 : NamedVasyuninInterval :=
{
  h := 5
  k := 22
  lower := (18870197/223030000)
  upper := (18914803/223030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_22_interval
}

theorem G5_23_formula : baezDuarteGramEntry 5 23 = vasyuninBEntry 5 23 := vasyuninBEntry_correct_axiom 5 23 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_23_eval :
    ((((12263023/149770000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 23) ∧
    (vasyuninBEntry 5 23 ≤ (((12292977/149770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_523_formula_bound
  constructor <;> linarith

theorem G5_23_interval :
    ((((12263023/149770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 23) ∧
    (baezDuarteGramEntry 5 23 ≤ (((12292977/149770000) : ℚ) : ℝ)) := by
  rw [G5_23_formula]
  exact vasyuninBEntry_5_23_eval

def interval_5_23 : NamedVasyuninInterval :=
{
  h := 5
  k := 23
  lower := (12263023/149770000)
  upper := (12292977/149770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_23_interval
}

theorem G5_24_formula : baezDuarteGramEntry 5 24 = vasyuninBEntry 5 24 := vasyuninBEntry_correct_axiom 5 24 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_24_eval :
    ((((1583011/19890000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 24) ∧
    (vasyuninBEntry 5 24 ≤ (((1586989/19890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_524_formula_bound
  constructor <;> linarith

theorem G5_24_interval :
    ((((1583011/19890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 24) ∧
    (baezDuarteGramEntry 5 24 ≤ (((1586989/19890000) : ℚ) : ℝ)) := by
  rw [G5_24_formula]
  exact vasyuninBEntry_5_24_eval

def interval_5_24 : NamedVasyuninInterval :=
{
  h := 5
  k := 24
  lower := (1583011/19890000)
  upper := (1586989/19890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_24_interval
}

theorem G5_25_formula : baezDuarteGramEntry 5 25 = vasyuninBEntry 5 25 := vasyuninBEntry_correct_axiom 5 25 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_25_eval :
    ((((59434187/758130000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 25) ∧
    (vasyuninBEntry 5 25 ≤ (((59585813/758130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 5 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G5_25_interval :
    ((((59434187/758130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 25) ∧
    (baezDuarteGramEntry 5 25 ≤ (((59585813/758130000) : ℚ) : ℝ)) := by
  rw [G5_25_formula]
  exact vasyuninBEntry_5_25_eval

def interval_5_25 : NamedVasyuninInterval :=
{
  h := 5
  k := 25
  lower := (59434187/758130000)
  upper := (59585813/758130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_25_interval
}

theorem G5_26_formula : baezDuarteGramEntry 5 26 = vasyuninBEntry 5 26 := vasyuninBEntry_correct_axiom 5 26 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_26_eval :
    ((((13661797/182030000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 26) ∧
    (vasyuninBEntry 5 26 ≤ (((13698203/182030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_526_formula_bound
  constructor <;> linarith

theorem G5_26_interval :
    ((((13661797/182030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 26) ∧
    (baezDuarteGramEntry 5 26 ≤ (((13698203/182030000) : ℚ) : ℝ)) := by
  rw [G5_26_formula]
  exact vasyuninBEntry_5_26_eval

def interval_5_26 : NamedVasyuninInterval :=
{
  h := 5
  k := 26
  lower := (13661797/182030000)
  upper := (13698203/182030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_26_interval
}

theorem G5_27_formula : baezDuarteGramEntry 5 27 = vasyuninBEntry 5 27 := vasyuninBEntry_correct_axiom 5 27 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_27_eval :
    ((((8113849/111510000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 27) ∧
    (vasyuninBEntry 5 27 ≤ (((8136151/111510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_527_formula_bound
  constructor <;> linarith

theorem G5_27_interval :
    ((((8113849/111510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 27) ∧
    (baezDuarteGramEntry 5 27 ≤ (((8136151/111510000) : ℚ) : ℝ)) := by
  rw [G5_27_formula]
  exact vasyuninBEntry_5_27_eval

def interval_5_27 : NamedVasyuninInterval :=
{
  h := 5
  k := 27
  lower := (8113849/111510000)
  upper := (8136151/111510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_27_interval
}

theorem G5_28_formula : baezDuarteGramEntry 5 28 = vasyuninBEntry 5 28 := vasyuninBEntry_correct_axiom 5 28 (by norm_num) (by norm_num)

theorem vasyuninBEntry_5_28_eval :
    ((((1402619/19810000) : ℚ) : ℝ) ≤ vasyuninBEntry 5 28) ∧
    (vasyuninBEntry 5 28 ≤ (((1406581/19810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_528_formula_bound
  constructor <;> linarith

theorem G5_28_interval :
    ((((1402619/19810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 5 28) ∧
    (baezDuarteGramEntry 5 28 ≤ (((1406581/19810000) : ℚ) : ℝ)) := by
  rw [G5_28_formula]
  exact vasyuninBEntry_5_28_eval

def interval_5_28 : NamedVasyuninInterval :=
{
  h := 5
  k := 28
  lower := (1402619/19810000)
  upper := (1406581/19810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G5_28_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
