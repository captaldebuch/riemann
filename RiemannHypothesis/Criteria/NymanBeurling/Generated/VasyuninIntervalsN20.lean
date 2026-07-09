import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20
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

theorem G6_7_formula : baezDuarteGramEntry 6 7 = vasyuninBEntry 6 7 := vasyuninBEntry_correct_axiom 6 7 (by norm_num) (by norm_num)

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

theorem G6_8_formula : baezDuarteGramEntry 6 8 = vasyuninBEntry 6 8 := vasyuninBEntry_correct_axiom 6 8 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_8_eval :
    ((((6315993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 8) ∧
    (vasyuninBEntry 6 8 ≤ (((6324007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G6_9_formula : baezDuarteGramEntry 6 9 = vasyuninBEntry 6 9 := vasyuninBEntry_correct_axiom 6 9 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_9_eval :
    ((((71076627/483730000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 9) ∧
    (vasyuninBEntry 6 9 ≤ (((71173373/483730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 3 (by norm_num) (by norm_num) (by norm_num)
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

theorem G6_10_formula : baezDuarteGramEntry 6 10 = vasyuninBEntry 6 10 := vasyuninBEntry_correct_axiom 6 10 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_10_eval :
    ((((40310507/294930000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 10) ∧
    (vasyuninBEntry 6 10 ≤ (((40369493/294930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G6_11_formula : baezDuarteGramEntry 6 11 = vasyuninBEntry 6 11 := vasyuninBEntry_correct_axiom 6 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_11_eval :
    ((((38255551/294490000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 11) ∧
    (vasyuninBEntry 6 11 ≤ (((38314449/294490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_611_formula_bound
  constructor <;> linarith

theorem G6_11_interval :
    ((((38255551/294490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 11) ∧
    (baezDuarteGramEntry 6 11 ≤ (((38314449/294490000) : ℚ) : ℝ)) := by
  rw [G6_11_formula]
  exact vasyuninBEntry_6_11_eval

def interval_6_11 : NamedVasyuninInterval :=
{
  h := 6
  k := 11
  lower := (38255551/294490000)
  upper := (38314449/294490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_11_interval
}

theorem G6_12_formula : baezDuarteGramEntry 6 12 = vasyuninBEntry 6 12 := vasyuninBEntry_correct_axiom 6 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_12_eval :
    ((((56760863/441370000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 12) ∧
    (vasyuninBEntry 6 12 ≤ (((56849137/441370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G6_12_interval :
    ((((56760863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 12) ∧
    (baezDuarteGramEntry 6 12 ≤ (((56849137/441370000) : ℚ) : ℝ)) := by
  rw [G6_12_formula]
  exact vasyuninBEntry_6_12_eval

def interval_6_12 : NamedVasyuninInterval :=
{
  h := 6
  k := 12
  lower := (56760863/441370000)
  upper := (56849137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_12_interval
}

theorem G6_13_formula : baezDuarteGramEntry 6 13 = vasyuninBEntry 6 13 := vasyuninBEntry_correct_axiom 6 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_13_eval :
    ((((12443359/106410000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 13) ∧
    (vasyuninBEntry 6 13 ≤ (((12464641/106410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_613_formula_bound
  constructor <;> linarith

theorem G6_13_interval :
    ((((12443359/106410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 13) ∧
    (baezDuarteGramEntry 6 13 ≤ (((12464641/106410000) : ℚ) : ℝ)) := by
  rw [G6_13_formula]
  exact vasyuninBEntry_6_13_eval

def interval_6_13 : NamedVasyuninInterval :=
{
  h := 6
  k := 13
  lower := (12443359/106410000)
  upper := (12464641/106410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_13_interval
}

theorem G6_14_formula : baezDuarteGramEntry 6 14 = vasyuninBEntry 6 14 := vasyuninBEntry_correct_axiom 6 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_14_eval :
    ((((2713939/24610000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 14) ∧
    (vasyuninBEntry 6 14 ≤ (((2718861/24610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 7 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_14_interval :
    ((((2713939/24610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 14) ∧
    (baezDuarteGramEntry 6 14 ≤ (((2718861/24610000) : ℚ) : ℝ)) := by
  rw [G6_14_formula]
  exact vasyuninBEntry_6_14_eval

def interval_6_14 : NamedVasyuninInterval :=
{
  h := 6
  k := 14
  lower := (2713939/24610000)
  upper := (2718861/24610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_14_interval
}

theorem G6_15_formula : baezDuarteGramEntry 6 15 = vasyuninBEntry 6 15 := vasyuninBEntry_correct_axiom 6 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_15_eval :
    ((((12158461/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 15) ∧
    (vasyuninBEntry 6 15 ≤ (((12181539/115390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G6_15_interval :
    ((((12158461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 15) ∧
    (baezDuarteGramEntry 6 15 ≤ (((12181539/115390000) : ℚ) : ℝ)) := by
  rw [G6_15_formula]
  exact vasyuninBEntry_6_15_eval

def interval_6_15 : NamedVasyuninInterval :=
{
  h := 6
  k := 15
  lower := (12158461/115390000)
  upper := (12181539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_15_interval
}

theorem G6_16_formula : baezDuarteGramEntry 6 16 = vasyuninBEntry 6 16 := vasyuninBEntry_correct_axiom 6 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_16_eval :
    ((((4012883/39920000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 16) ∧
    (vasyuninBEntry 6 16 ≤ (((4020867/39920000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 8 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_16_interval :
    ((((4012883/39920000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 16) ∧
    (baezDuarteGramEntry 6 16 ≤ (((4020867/39920000) : ℚ) : ℝ)) := by
  rw [G6_16_formula]
  exact vasyuninBEntry_6_16_eval

def interval_6_16 : NamedVasyuninInterval :=
{
  h := 6
  k := 16
  lower := (4012883/39920000)
  upper := (4020867/39920000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_16_interval
}

theorem G6_17_formula : baezDuarteGramEntry 6 17 = vasyuninBEntry 6 17 := vasyuninBEntry_correct_axiom 6 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_17_eval :
    ((((79068453/815470000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 17) ∧
    (vasyuninBEntry 6 17 ≤ (((79231547/815470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_617_formula_bound
  constructor <;> linarith

theorem G6_17_interval :
    ((((79068453/815470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 17) ∧
    (baezDuarteGramEntry 6 17 ≤ (((79231547/815470000) : ℚ) : ℝ)) := by
  rw [G6_17_formula]
  exact vasyuninBEntry_6_17_eval

def interval_6_17 : NamedVasyuninInterval :=
{
  h := 6
  k := 17
  lower := (79068453/815470000)
  upper := (79231547/815470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_17_interval
}

theorem G6_18_formula : baezDuarteGramEntry 6 18 = vasyuninBEntry 6 18 := vasyuninBEntry_correct_axiom 6 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_18_eval :
    ((((48279569/504310000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 18) ∧
    (vasyuninBEntry 6 18 ≤ (((48380431/504310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 3 6 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 6)
  constructor <;> linarith

theorem G6_18_interval :
    ((((48279569/504310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 18) ∧
    (baezDuarteGramEntry 6 18 ≤ (((48380431/504310000) : ℚ) : ℝ)) := by
  rw [G6_18_formula]
  exact vasyuninBEntry_6_18_eval

def interval_6_18 : NamedVasyuninInterval :=
{
  h := 6
  k := 18
  lower := (48279569/504310000)
  upper := (48380431/504310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_18_interval
}

theorem G6_19_formula : baezDuarteGramEntry 6 19 = vasyuninBEntry 6 19 := vasyuninBEntry_correct_axiom 6 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_19_eval :
    ((((16491647/183530000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 19) ∧
    (vasyuninBEntry 6 19 ≤ (((16528353/183530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_619_formula_bound
  constructor <;> linarith

theorem G6_19_interval :
    ((((16491647/183530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 19) ∧
    (baezDuarteGramEntry 6 19 ≤ (((16528353/183530000) : ℚ) : ℝ)) := by
  rw [G6_19_formula]
  exact vasyuninBEntry_6_19_eval

def interval_6_19 : NamedVasyuninInterval :=
{
  h := 6
  k := 19
  lower := (16491647/183530000)
  upper := (16528353/183530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_19_interval
}

theorem G6_20_formula : baezDuarteGramEntry 6 20 = vasyuninBEntry 6 20 := vasyuninBEntry_correct_axiom 6 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_6_20_eval :
    ((((32207631/373690000) : ℚ) : ℝ) ≤ vasyuninBEntry 6 20) ∧
    (vasyuninBEntry 6 20 ≤ (((32282369/373690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 10 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G6_20_interval :
    ((((32207631/373690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 6 20) ∧
    (baezDuarteGramEntry 6 20 ≤ (((32282369/373690000) : ℚ) : ℝ)) := by
  rw [G6_20_formula]
  exact vasyuninBEntry_6_20_eval

def interval_6_20 : NamedVasyuninInterval :=
{
  h := 6
  k := 20
  lower := (32207631/373690000)
  upper := (32282369/373690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G6_20_interval
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

theorem G7_8_formula : baezDuarteGramEntry 7 8 = vasyuninBEntry 7 8 := vasyuninBEntry_correct_axiom 7 8 (by norm_num) (by norm_num)

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

theorem G7_9_formula : baezDuarteGramEntry 7 9 = vasyuninBEntry 7 9 := vasyuninBEntry_correct_axiom 7 9 (by norm_num) (by norm_num)

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

theorem G7_10_formula : baezDuarteGramEntry 7 10 = vasyuninBEntry 7 10 := vasyuninBEntry_correct_axiom 7 10 (by norm_num) (by norm_num)

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

theorem G7_11_formula : baezDuarteGramEntry 7 11 = vasyuninBEntry 7 11 := vasyuninBEntry_correct_axiom 7 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_11_eval :
    ((((96270517/794830000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 11) ∧
    (vasyuninBEntry 7 11 ≤ (((96429483/794830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_711_formula_bound
  constructor <;> linarith

theorem G7_11_interval :
    ((((96270517/794830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 11) ∧
    (baezDuarteGramEntry 7 11 ≤ (((96429483/794830000) : ℚ) : ℝ)) := by
  rw [G7_11_formula]
  exact vasyuninBEntry_7_11_eval

def interval_7_11 : NamedVasyuninInterval :=
{
  h := 7
  k := 11
  lower := (96270517/794830000)
  upper := (96429483/794830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_11_interval
}

theorem G7_12_formula : baezDuarteGramEntry 7 12 = vasyuninBEntry 7 12 := vasyuninBEntry_correct_axiom 7 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_12_eval :
    ((((94797571/824290000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 12) ∧
    (vasyuninBEntry 7 12 ≤ (((94962429/824290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_712_formula_bound
  constructor <;> linarith

theorem G7_12_interval :
    ((((94797571/824290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 12) ∧
    (baezDuarteGramEntry 7 12 ≤ (((94962429/824290000) : ℚ) : ℝ)) := by
  rw [G7_12_formula]
  exact vasyuninBEntry_7_12_eval

def interval_7_12 : NamedVasyuninInterval :=
{
  h := 7
  k := 12
  lower := (94797571/824290000)
  upper := (94962429/824290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_12_interval
}

theorem G7_13_formula : baezDuarteGramEntry 7 13 = vasyuninBEntry 7 13 := vasyuninBEntry_correct_axiom 7 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_13_eval :
    ((((13636439/123110000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 13) ∧
    (vasyuninBEntry 7 13 ≤ (((13661061/123110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_713_formula_bound
  constructor <;> linarith

theorem G7_13_interval :
    ((((13636439/123110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 13) ∧
    (baezDuarteGramEntry 7 13 ≤ (((13661061/123110000) : ℚ) : ℝ)) := by
  rw [G7_13_formula]
  exact vasyuninBEntry_7_13_eval

def interval_7_13 : NamedVasyuninInterval :=
{
  h := 7
  k := 13
  lower := (13636439/123110000)
  upper := (13661061/123110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_13_interval
}

theorem G7_14_formula : baezDuarteGramEntry 7 14 = vasyuninBEntry 7 14 := vasyuninBEntry_correct_axiom 7 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_14_eval :
    ((((52417441/475590000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 14) ∧
    (vasyuninBEntry 7 14 ≤ (((52512559/475590000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 7 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G7_14_interval :
    ((((52417441/475590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 14) ∧
    (baezDuarteGramEntry 7 14 ≤ (((52512559/475590000) : ℚ) : ℝ)) := by
  rw [G7_14_formula]
  exact vasyuninBEntry_7_14_eval

def interval_7_14 : NamedVasyuninInterval :=
{
  h := 7
  k := 14
  lower := (52417441/475590000)
  upper := (52512559/475590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_14_interval
}

theorem G7_15_formula : baezDuarteGramEntry 7 15 = vasyuninBEntry 7 15 := vasyuninBEntry_correct_axiom 7 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_15_eval :
    ((((28931421/285790000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 15) ∧
    (vasyuninBEntry 7 15 ≤ (((28988579/285790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_715_formula_bound
  constructor <;> linarith

theorem G7_15_interval :
    ((((28931421/285790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 15) ∧
    (baezDuarteGramEntry 7 15 ≤ (((28988579/285790000) : ℚ) : ℝ)) := by
  rw [G7_15_formula]
  exact vasyuninBEntry_7_15_eval

def interval_7_15 : NamedVasyuninInterval :=
{
  h := 7
  k := 15
  lower := (28931421/285790000)
  upper := (28988579/285790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_15_interval
}

theorem G7_16_formula : baezDuarteGramEntry 7 16 = vasyuninBEntry 7 16 := vasyuninBEntry_correct_axiom 7 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_16_eval :
    ((((1045709/10910000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 16) ∧
    (vasyuninBEntry 7 16 ≤ (((1047891/10910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_716_formula_bound
  constructor <;> linarith

theorem G7_16_interval :
    ((((1045709/10910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 16) ∧
    (baezDuarteGramEntry 7 16 ≤ (((1047891/10910000) : ℚ) : ℝ)) := by
  rw [G7_16_formula]
  exact vasyuninBEntry_7_16_eval

def interval_7_16 : NamedVasyuninInterval :=
{
  h := 7
  k := 16
  lower := (1045709/10910000)
  upper := (1047891/10910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_16_interval
}

theorem G7_17_formula : baezDuarteGramEntry 7 17 = vasyuninBEntry 7 17 := vasyuninBEntry_correct_axiom 7 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_17_eval :
    ((((41439803/451970000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 17) ∧
    (vasyuninBEntry 7 17 ≤ (((41530197/451970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_717_formula_bound
  constructor <;> linarith

theorem G7_17_interval :
    ((((41439803/451970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 17) ∧
    (baezDuarteGramEntry 7 17 ≤ (((41530197/451970000) : ℚ) : ℝ)) := by
  rw [G7_17_formula]
  exact vasyuninBEntry_7_17_eval

def interval_7_17 : NamedVasyuninInterval :=
{
  h := 7
  k := 17
  lower := (41439803/451970000)
  upper := (41530197/451970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_17_interval
}

theorem G7_18_formula : baezDuarteGramEntry 7 18 = vasyuninBEntry 7 18 := vasyuninBEntry_correct_axiom 7 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_18_eval :
    ((((42916311/486890000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 18) ∧
    (vasyuninBEntry 7 18 ≤ (((43013689/486890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_718_formula_bound
  constructor <;> linarith

theorem G7_18_interval :
    ((((42916311/486890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 18) ∧
    (baezDuarteGramEntry 7 18 ≤ (((43013689/486890000) : ℚ) : ℝ)) := by
  rw [G7_18_formula]
  exact vasyuninBEntry_7_18_eval

def interval_7_18 : NamedVasyuninInterval :=
{
  h := 7
  k := 18
  lower := (42916311/486890000)
  upper := (43013689/486890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_18_interval
}

theorem G7_19_formula : baezDuarteGramEntry 7 19 = vasyuninBEntry 7 19 := vasyuninBEntry_correct_axiom 7 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_19_eval :
    ((((2231877/26230000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 19) ∧
    (vasyuninBEntry 7 19 ≤ (((2237123/26230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_719_formula_bound
  constructor <;> linarith

theorem G7_19_interval :
    ((((2231877/26230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 19) ∧
    (baezDuarteGramEntry 7 19 ≤ (((2237123/26230000) : ℚ) : ℝ)) := by
  rw [G7_19_formula]
  exact vasyuninBEntry_7_19_eval

def interval_7_19 : NamedVasyuninInterval :=
{
  h := 7
  k := 19
  lower := (2231877/26230000)
  upper := (2237123/26230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_19_interval
}

theorem G7_20_formula : baezDuarteGramEntry 7 20 = vasyuninBEntry 7 20 := vasyuninBEntry_correct_axiom 7 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_7_20_eval :
    ((((78045703/942970000) : ℚ) : ℝ) ≤ vasyuninBEntry 7 20) ∧
    (vasyuninBEntry 7 20 ≤ (((78234297/942970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_720_formula_bound
  constructor <;> linarith

theorem G7_20_interval :
    ((((78045703/942970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 7 20) ∧
    (baezDuarteGramEntry 7 20 ≤ (((78234297/942970000) : ℚ) : ℝ)) := by
  rw [G7_20_formula]
  exact vasyuninBEntry_7_20_eval

def interval_7_20 : NamedVasyuninInterval :=
{
  h := 7
  k := 20
  lower := (78045703/942970000)
  upper := (78234297/942970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G7_20_interval
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

theorem G8_9_formula : baezDuarteGramEntry 8 9 = vasyuninBEntry 8 9 := vasyuninBEntry_correct_axiom 8 9 (by norm_num) (by norm_num)

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

theorem G8_10_formula : baezDuarteGramEntry 8 10 = vasyuninBEntry 8 10 := vasyuninBEntry_correct_axiom 8 10 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_10_eval :
    ((((12715961/102890000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 10) ∧
    (vasyuninBEntry 8 10 ≤ (((12736539/102890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G8_11_formula : baezDuarteGramEntry 8 11 = vasyuninBEntry 8 11 := vasyuninBEntry_correct_axiom 8 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_11_eval :
    ((((27808387/241130000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 11) ∧
    (vasyuninBEntry 8 11 ≤ (((27856613/241130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_811_formula_bound
  constructor <;> linarith

theorem G8_11_interval :
    ((((27808387/241130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 11) ∧
    (baezDuarteGramEntry 8 11 ≤ (((27856613/241130000) : ℚ) : ℝ)) := by
  rw [G8_11_formula]
  exact vasyuninBEntry_8_11_eval

def interval_8_11 : NamedVasyuninInterval :=
{
  h := 8
  k := 11
  lower := (27808387/241130000)
  upper := (27856613/241130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_11_interval
}

theorem G8_12_formula : baezDuarteGramEntry 8 12 = vasyuninBEntry 8 12 := vasyuninBEntry_correct_axiom 8 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_12_eval :
    ((((14656697/133030000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 12) ∧
    (vasyuninBEntry 8 12 ≤ (((14683303/133030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G8_12_interval :
    ((((14656697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 12) ∧
    (baezDuarteGramEntry 8 12 ≤ (((14683303/133030000) : ℚ) : ℝ)) := by
  rw [G8_12_formula]
  exact vasyuninBEntry_8_12_eval

def interval_8_12 : NamedVasyuninInterval :=
{
  h := 8
  k := 12
  lower := (14656697/133030000)
  upper := (14683303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_12_interval
}

theorem G8_13_formula : baezDuarteGramEntry 8 13 = vasyuninBEntry 8 13 := vasyuninBEntry_correct_axiom 8 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_13_eval :
    ((((9109969/87810000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 13) ∧
    (vasyuninBEntry 8 13 ≤ (((9127531/87810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_813_formula_bound
  constructor <;> linarith

theorem G8_13_interval :
    ((((9109969/87810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 13) ∧
    (baezDuarteGramEntry 8 13 ≤ (((9127531/87810000) : ℚ) : ℝ)) := by
  rw [G8_13_formula]
  exact vasyuninBEntry_8_13_eval

def interval_8_13 : NamedVasyuninInterval :=
{
  h := 8
  k := 13
  lower := (9109969/87810000)
  upper := (9127531/87810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_13_interval
}

theorem G8_14_formula : baezDuarteGramEntry 8 14 = vasyuninBEntry 8 14 := vasyuninBEntry_correct_axiom 8 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_14_eval :
    ((((24685219/247810000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 14) ∧
    (vasyuninBEntry 8 14 ≤ (((24734781/247810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 7 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_14_interval :
    ((((24685219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 14) ∧
    (baezDuarteGramEntry 8 14 ≤ (((24734781/247810000) : ℚ) : ℝ)) := by
  rw [G8_14_formula]
  exact vasyuninBEntry_8_14_eval

def interval_8_14 : NamedVasyuninInterval :=
{
  h := 8
  k := 14
  lower := (24685219/247810000)
  upper := (24734781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_14_interval
}

theorem G8_15_formula : baezDuarteGramEntry 8 15 = vasyuninBEntry 8 15 := vasyuninBEntry_correct_axiom 8 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_15_eval :
    ((((52665471/545290000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 15) ∧
    (vasyuninBEntry 8 15 ≤ (((52774529/545290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_815_formula_bound
  constructor <;> linarith

theorem G8_15_interval :
    ((((52665471/545290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 15) ∧
    (baezDuarteGramEntry 8 15 ≤ (((52774529/545290000) : ℚ) : ℝ)) := by
  rw [G8_15_formula]
  exact vasyuninBEntry_8_15_eval

def interval_8_15 : NamedVasyuninInterval :=
{
  h := 8
  k := 15
  lower := (52665471/545290000)
  upper := (52774529/545290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_15_interval
}

theorem G8_16_formula : baezDuarteGramEntry 8 16 = vasyuninBEntry 8 16 := vasyuninBEntry_correct_axiom 8 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_16_eval :
    ((((7022717/72830000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 16) ∧
    (vasyuninBEntry 8 16 ≤ (((7037283/72830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 8 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G8_16_interval :
    ((((7022717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 16) ∧
    (baezDuarteGramEntry 8 16 ≤ (((7037283/72830000) : ℚ) : ℝ)) := by
  rw [G8_16_formula]
  exact vasyuninBEntry_8_16_eval

def interval_8_16 : NamedVasyuninInterval :=
{
  h := 8
  k := 16
  lower := (7022717/72830000)
  upper := (7037283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_16_interval
}

theorem G8_17_formula : baezDuarteGramEntry 8 17 = vasyuninBEntry 8 17 := vasyuninBEntry_correct_axiom 8 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_17_eval :
    ((((10578151/118490000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 17) ∧
    (vasyuninBEntry 8 17 ≤ (((10601849/118490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_817_formula_bound
  constructor <;> linarith

theorem G8_17_interval :
    ((((10578151/118490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 17) ∧
    (baezDuarteGramEntry 8 17 ≤ (((10601849/118490000) : ℚ) : ℝ)) := by
  rw [G8_17_formula]
  exact vasyuninBEntry_8_17_eval

def interval_8_17 : NamedVasyuninInterval :=
{
  h := 8
  k := 17
  lower := (10578151/118490000)
  upper := (10601849/118490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_17_interval
}

theorem G8_18_formula : baezDuarteGramEntry 8 18 = vasyuninBEntry 8 18 := vasyuninBEntry_correct_axiom 8 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_18_eval :
    ((((81474103/958970000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 18) ∧
    (vasyuninBEntry 8 18 ≤ (((81665897/958970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 9 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G8_18_interval :
    ((((81474103/958970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 18) ∧
    (baezDuarteGramEntry 8 18 ≤ (((81665897/958970000) : ℚ) : ℝ)) := by
  rw [G8_18_formula]
  exact vasyuninBEntry_8_18_eval

def interval_8_18 : NamedVasyuninInterval :=
{
  h := 8
  k := 18
  lower := (81474103/958970000)
  upper := (81665897/958970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_18_interval
}

theorem G8_19_formula : baezDuarteGramEntry 8 19 = vasyuninBEntry 8 19 := vasyuninBEntry_correct_axiom 8 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_19_eval :
    ((((36585097/449030000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 19) ∧
    (vasyuninBEntry 8 19 ≤ (((36674903/449030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_819_formula_bound
  constructor <;> linarith

theorem G8_19_interval :
    ((((36585097/449030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 19) ∧
    (baezDuarteGramEntry 8 19 ≤ (((36674903/449030000) : ℚ) : ℝ)) := by
  rw [G8_19_formula]
  exact vasyuninBEntry_8_19_eval

def interval_8_19 : NamedVasyuninInterval :=
{
  h := 8
  k := 19
  lower := (36585097/449030000)
  upper := (36674903/449030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_19_interval
}

theorem G8_20_formula : baezDuarteGramEntry 8 20 = vasyuninBEntry 8 20 := vasyuninBEntry_correct_axiom 8 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_8_20_eval :
    ((((9115961/115390000) : ℚ) : ℝ) ≤ vasyuninBEntry 8 20) ∧
    (vasyuninBEntry 8 20 ≤ (((9139039/115390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G8_20_interval :
    ((((9115961/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 8 20) ∧
    (baezDuarteGramEntry 8 20 ≤ (((9139039/115390000) : ℚ) : ℝ)) := by
  rw [G8_20_formula]
  exact vasyuninBEntry_8_20_eval

def interval_8_20 : NamedVasyuninInterval :=
{
  h := 8
  k := 20
  lower := (9115961/115390000)
  upper := (9139039/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G8_20_interval
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

theorem G9_10_formula : baezDuarteGramEntry 9 10 = vasyuninBEntry 9 10 := vasyuninBEntry_correct_axiom 9 10 (by norm_num) (by norm_num)

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

theorem G9_11_formula : baezDuarteGramEntry 9 11 = vasyuninBEntry 9 11 := vasyuninBEntry_correct_axiom 9 11 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_11_eval :
    ((((5335219/47810000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 11) ∧
    (vasyuninBEntry 9 11 ≤ (((5344781/47810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_911_formula_bound
  constructor <;> linarith

theorem G9_11_interval :
    ((((5335219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 11) ∧
    (baezDuarteGramEntry 9 11 ≤ (((5344781/47810000) : ℚ) : ℝ)) := by
  rw [G9_11_formula]
  exact vasyuninBEntry_9_11_eval

def interval_9_11 : NamedVasyuninInterval :=
{
  h := 9
  k := 11
  lower := (5335219/47810000)
  upper := (5344781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_11_interval
}

theorem G9_12_formula : baezDuarteGramEntry 9 12 = vasyuninBEntry 9 12 := vasyuninBEntry_correct_axiom 9 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_12_eval :
    ((((12627979/120210000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 12) ∧
    (vasyuninBEntry 9 12 ≤ (((12652021/120210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_12_interval :
    ((((12627979/120210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 12) ∧
    (baezDuarteGramEntry 9 12 ≤ (((12652021/120210000) : ℚ) : ℝ)) := by
  rw [G9_12_formula]
  exact vasyuninBEntry_9_12_eval

def interval_9_12 : NamedVasyuninInterval :=
{
  h := 9
  k := 12
  lower := (12627979/120210000)
  upper := (12652021/120210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_12_interval
}

theorem G9_13_formula : baezDuarteGramEntry 9 13 = vasyuninBEntry 9 13 := vasyuninBEntry_correct_axiom 9 13 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_13_eval :
    ((((16962929/170710000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 13) ∧
    (vasyuninBEntry 9 13 ≤ (((16997071/170710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_913_formula_bound
  constructor <;> linarith

theorem G9_13_interval :
    ((((16962929/170710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 13) ∧
    (baezDuarteGramEntry 9 13 ≤ (((16997071/170710000) : ℚ) : ℝ)) := by
  rw [G9_13_formula]
  exact vasyuninBEntry_9_13_eval

def interval_9_13 : NamedVasyuninInterval :=
{
  h := 9
  k := 13
  lower := (16962929/170710000)
  upper := (16997071/170710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_13_interval
}

theorem G9_14_formula : baezDuarteGramEntry 9 14 = vasyuninBEntry 9 14 := vasyuninBEntry_correct_axiom 9 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_14_eval :
    ((((23572643/248570000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 14) ∧
    (vasyuninBEntry 9 14 ≤ (((23622357/248570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_914_formula_bound
  constructor <;> linarith

theorem G9_14_interval :
    ((((23572643/248570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 14) ∧
    (baezDuarteGramEntry 9 14 ≤ (((23622357/248570000) : ℚ) : ℝ)) := by
  rw [G9_14_formula]
  exact vasyuninBEntry_9_14_eval

def interval_9_14 : NamedVasyuninInterval :=
{
  h := 9
  k := 14
  lower := (23572643/248570000)
  upper := (23622357/248570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_14_interval
}

theorem G9_15_formula : baezDuarteGramEntry 9 15 = vasyuninBEntry 9 15 := vasyuninBEntry_correct_axiom 9 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_15_eval :
    ((((80591521/884790000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 15) ∧
    (vasyuninBEntry 9 15 ≤ (((80768479/884790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G9_15_interval :
    ((((80591521/884790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 15) ∧
    (baezDuarteGramEntry 9 15 ≤ (((80768479/884790000) : ℚ) : ℝ)) := by
  rw [G9_15_formula]
  exact vasyuninBEntry_9_15_eval

def interval_9_15 : NamedVasyuninInterval :=
{
  h := 9
  k := 15
  lower := (80591521/884790000)
  upper := (80768479/884790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_15_interval
}

theorem G9_16_formula : baezDuarteGramEntry 9 16 = vasyuninBEntry 9 16 := vasyuninBEntry_correct_axiom 9 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_16_eval :
    ((((12042277/137230000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 16) ∧
    (vasyuninBEntry 9 16 ≤ (((12069723/137230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_916_formula_bound
  constructor <;> linarith

theorem G9_16_interval :
    ((((12042277/137230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 16) ∧
    (baezDuarteGramEntry 9 16 ≤ (((12069723/137230000) : ℚ) : ℝ)) := by
  rw [G9_16_formula]
  exact vasyuninBEntry_9_16_eval

def interval_9_16 : NamedVasyuninInterval :=
{
  h := 9
  k := 16
  lower := (12042277/137230000)
  upper := (12069723/137230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_16_interval
}

theorem G9_17_formula : baezDuarteGramEntry 9 17 = vasyuninBEntry 9 17 := vasyuninBEntry_correct_axiom 9 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_17_eval :
    ((((25929723/302770000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 17) ∧
    (vasyuninBEntry 9 17 ≤ (((25990277/302770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_917_formula_bound
  constructor <;> linarith

theorem G9_17_interval :
    ((((25929723/302770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 17) ∧
    (baezDuarteGramEntry 9 17 ≤ (((25990277/302770000) : ℚ) : ℝ)) := by
  rw [G9_17_formula]
  exact vasyuninBEntry_9_17_eval

def interval_9_17 : NamedVasyuninInterval :=
{
  h := 9
  k := 17
  lower := (25929723/302770000)
  upper := (25990277/302770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_17_interval
}

theorem G9_18_formula : baezDuarteGramEntry 9 18 = vasyuninBEntry 9 18 := vasyuninBEntry_correct_axiom 9 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_18_eval :
    ((((37825863/441370000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 18) ∧
    (vasyuninBEntry 9 18 ≤ (((37914137/441370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 9 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 9)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 9)
  constructor <;> linarith

theorem G9_18_interval :
    ((((37825863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 18) ∧
    (baezDuarteGramEntry 9 18 ≤ (((37914137/441370000) : ℚ) : ℝ)) := by
  rw [G9_18_formula]
  exact vasyuninBEntry_9_18_eval

def interval_9_18 : NamedVasyuninInterval :=
{
  h := 9
  k := 18
  lower := (37825863/441370000)
  upper := (37914137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_18_interval
}

theorem G9_19_formula : baezDuarteGramEntry 9 19 = vasyuninBEntry 9 19 := vasyuninBEntry_correct_axiom 9 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_19_eval :
    ((((25068609/313910000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 19) ∧
    (vasyuninBEntry 9 19 ≤ (((25131391/313910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_919_formula_bound
  constructor <;> linarith

theorem G9_19_interval :
    ((((25068609/313910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 19) ∧
    (baezDuarteGramEntry 9 19 ≤ (((25131391/313910000) : ℚ) : ℝ)) := by
  rw [G9_19_formula]
  exact vasyuninBEntry_9_19_eval

def interval_9_19 : NamedVasyuninInterval :=
{
  h := 9
  k := 19
  lower := (25068609/313910000)
  upper := (25131391/313910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_19_interval
}

theorem G9_20_formula : baezDuarteGramEntry 9 20 = vasyuninBEntry 9 20 := vasyuninBEntry_correct_axiom 9 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_9_20_eval :
    ((((6915927/90730000) : ℚ) : ℝ) ≤ vasyuninBEntry 9 20) ∧
    (vasyuninBEntry 9 20 ≤ (((6934073/90730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_920_formula_bound
  constructor <;> linarith

theorem G9_20_interval :
    ((((6915927/90730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 9 20) ∧
    (baezDuarteGramEntry 9 20 ≤ (((6934073/90730000) : ℚ) : ℝ)) := by
  rw [G9_20_formula]
  exact vasyuninBEntry_9_20_eval

def interval_9_20 : NamedVasyuninInterval :=
{
  h := 9
  k := 20
  lower := (6915927/90730000)
  upper := (6934073/90730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G9_20_interval
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

theorem G10_11_formula : baezDuarteGramEntry 10 11 = vasyuninBEntry 10 11 := vasyuninBEntry_correct_axiom 10 11 (by norm_num) (by norm_num)

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

theorem G10_12_formula : baezDuarteGramEntry 10 12 = vasyuninBEntry 10 12 := vasyuninBEntry_correct_axiom 10 12 (by norm_num) (by norm_num)

theorem vasyuninBEntry_10_12_eval :
    ((((17482859/171410000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 12) ∧
    (vasyuninBEntry 10 12 ≤ (((17517141/171410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G10_13_formula : baezDuarteGramEntry 10 13 = vasyuninBEntry 10 13 := vasyuninBEntry_correct_axiom 10 13 (by norm_num) (by norm_num)

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

theorem G10_14_formula : baezDuarteGramEntry 10 14 = vasyuninBEntry 10 14 := vasyuninBEntry_correct_axiom 10 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_10_14_eval :
    ((((18160087/199130000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 14) ∧
    (vasyuninBEntry 10 14 ≤ (((18199913/199130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 7 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G10_15_formula : baezDuarteGramEntry 10 15 = vasyuninBEntry 10 15 := vasyuninBEntry_correct_axiom 10 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_10_15_eval :
    ((((2109169/23935000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 15) ∧
    (vasyuninBEntry 10 15 ≤ (((528489/5983750) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 5 (by norm_num) (by norm_num) (by norm_num)
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

theorem G10_16_formula : baezDuarteGramEntry 10 16 = vasyuninBEntry 10 16 := vasyuninBEntry_correct_axiom 10 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_10_16_eval :
    ((((1256251/14990000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 16) ∧
    (vasyuninBEntry 10 16 ≤ (((1259249/14990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 8 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G10_17_formula : baezDuarteGramEntry 10 17 = vasyuninBEntry 10 17 := vasyuninBEntry_correct_axiom 10 17 (by norm_num) (by norm_num)

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

theorem G10_18_formula : baezDuarteGramEntry 10 18 = vasyuninBEntry 10 18 := vasyuninBEntry_correct_axiom 10 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_10_18_eval :
    ((((8609039/109610000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 18) ∧
    (vasyuninBEntry 10 18 ≤ (((8630961/109610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 9 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G10_19_formula : baezDuarteGramEntry 10 19 = vasyuninBEntry 10 19 := vasyuninBEntry_correct_axiom 10 19 (by norm_num) (by norm_num)

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

theorem G10_20_formula : baezDuarteGramEntry 10 20 = vasyuninBEntry 10 20 := vasyuninBEntry_correct_axiom 10 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_10_20_eval :
    ((((73694443/955570000) : ℚ) : ℝ) ≤ vasyuninBEntry 10 20) ∧
    (vasyuninBEntry 10 20 ≤ (((73885557/955570000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 10 (by norm_num) (by norm_num) (by norm_num)
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

theorem G11_12_formula : baezDuarteGramEntry 11 12 = vasyuninBEntry 11 12 := vasyuninBEntry_correct_axiom 11 12 (by norm_num) (by norm_num)

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

theorem G11_13_formula : baezDuarteGramEntry 11 13 = vasyuninBEntry 11 13 := vasyuninBEntry_correct_axiom 11 13 (by norm_num) (by norm_num)

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

theorem G11_14_formula : baezDuarteGramEntry 11 14 = vasyuninBEntry 11 14 := vasyuninBEntry_correct_axiom 11 14 (by norm_num) (by norm_num)

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

theorem G11_15_formula : baezDuarteGramEntry 11 15 = vasyuninBEntry 11 15 := vasyuninBEntry_correct_axiom 11 15 (by norm_num) (by norm_num)

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

theorem G11_16_formula : baezDuarteGramEntry 11 16 = vasyuninBEntry 11 16 := vasyuninBEntry_correct_axiom 11 16 (by norm_num) (by norm_num)

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

theorem G11_17_formula : baezDuarteGramEntry 11 17 = vasyuninBEntry 11 17 := vasyuninBEntry_correct_axiom 11 17 (by norm_num) (by norm_num)

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

theorem G11_18_formula : baezDuarteGramEntry 11 18 = vasyuninBEntry 11 18 := vasyuninBEntry_correct_axiom 11 18 (by norm_num) (by norm_num)

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

theorem G11_19_formula : baezDuarteGramEntry 11 19 = vasyuninBEntry 11 19 := vasyuninBEntry_correct_axiom 11 19 (by norm_num) (by norm_num)

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

theorem G11_20_formula : baezDuarteGramEntry 11 20 = vasyuninBEntry 11 20 := vasyuninBEntry_correct_axiom 11 20 (by norm_num) (by norm_num)

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

theorem G12_13_formula : baezDuarteGramEntry 12 13 = vasyuninBEntry 12 13 := vasyuninBEntry_correct_axiom 12 13 (by norm_num) (by norm_num)

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

theorem G12_14_formula : baezDuarteGramEntry 12 14 = vasyuninBEntry 12 14 := vasyuninBEntry_correct_axiom 12 14 (by norm_num) (by norm_num)

theorem vasyuninBEntry_12_14_eval :
    ((((40833059/469410000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 14) ∧
    (vasyuninBEntry 12 14 ≤ (((40926941/469410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_6_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 6 7 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G12_15_formula : baezDuarteGramEntry 12 15 = vasyuninBEntry 12 15 := vasyuninBEntry_correct_axiom 12 15 (by norm_num) (by norm_num)

theorem vasyuninBEntry_12_15_eval :
    ((((62534071/759290000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 15) ∧
    (vasyuninBEntry 12 15 ≤ (((62685929/759290000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 3 (by norm_num) (by norm_num) (by norm_num)
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

theorem G12_16_formula : baezDuarteGramEntry 12 16 = vasyuninBEntry 12 16 := vasyuninBEntry_correct_axiom 12 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_12_16_eval :
    ((((3155993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 16) ∧
    (vasyuninBEntry 12 16 ≤ (((3164007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 4 (by norm_num) (by norm_num) (by norm_num)
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

theorem G12_17_formula : baezDuarteGramEntry 12 17 = vasyuninBEntry 12 17 := vasyuninBEntry_correct_axiom 12 17 (by norm_num) (by norm_num)

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

theorem G12_18_formula : baezDuarteGramEntry 12 18 = vasyuninBEntry 12 18 := vasyuninBEntry_correct_axiom 12 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_12_18_eval :
    ((((9766697/133030000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 18) ∧
    (vasyuninBEntry 12 18 ≤ (((9793303/133030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 6 (by norm_num) (by norm_num) (by norm_num)
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

theorem G12_19_formula : baezDuarteGramEntry 12 19 = vasyuninBEntry 12 19 := vasyuninBEntry_correct_axiom 12 19 (by norm_num) (by norm_num)

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

theorem G12_20_formula : baezDuarteGramEntry 12 20 = vasyuninBEntry 12 20 := vasyuninBEntry_correct_axiom 12 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_12_20_eval :
    ((((20140507/294930000) : ℚ) : ℝ) ≤ vasyuninBEntry 12 20) ∧
    (vasyuninBEntry 12 20 ≤ (((20199493/294930000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 4 (by norm_num) (by norm_num) (by norm_num)
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

theorem G13_14_formula : baezDuarteGramEntry 13 14 = vasyuninBEntry 13 14 := vasyuninBEntry_correct_axiom 13 14 (by norm_num) (by norm_num)

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

theorem G13_15_formula : baezDuarteGramEntry 13 15 = vasyuninBEntry 13 15 := vasyuninBEntry_correct_axiom 13 15 (by norm_num) (by norm_num)

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

theorem G13_16_formula : baezDuarteGramEntry 13 16 = vasyuninBEntry 13 16 := vasyuninBEntry_correct_axiom 13 16 (by norm_num) (by norm_num)

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

theorem G13_17_formula : baezDuarteGramEntry 13 17 = vasyuninBEntry 13 17 := vasyuninBEntry_correct_axiom 13 17 (by norm_num) (by norm_num)

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

theorem G13_18_formula : baezDuarteGramEntry 13 18 = vasyuninBEntry 13 18 := vasyuninBEntry_correct_axiom 13 18 (by norm_num) (by norm_num)

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

theorem G13_19_formula : baezDuarteGramEntry 13 19 = vasyuninBEntry 13 19 := vasyuninBEntry_correct_axiom 13 19 (by norm_num) (by norm_num)

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

theorem G13_20_formula : baezDuarteGramEntry 13 20 = vasyuninBEntry 13 20 := vasyuninBEntry_correct_axiom 13 20 (by norm_num) (by norm_num)

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

theorem G14_15_formula : baezDuarteGramEntry 14 15 = vasyuninBEntry 14 15 := vasyuninBEntry_correct_axiom 14 15 (by norm_num) (by norm_num)

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

theorem G14_16_formula : baezDuarteGramEntry 14 16 = vasyuninBEntry 14 16 := vasyuninBEntry_correct_axiom 14 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_14_16_eval :
    ((((55417003/729970000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 16) ∧
    (vasyuninBEntry 14 16 ≤ (((55562997/729970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 8 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G14_17_formula : baezDuarteGramEntry 14 17 = vasyuninBEntry 14 17 := vasyuninBEntry_correct_axiom 14 17 (by norm_num) (by norm_num)

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

theorem G14_18_formula : baezDuarteGramEntry 14 18 = vasyuninBEntry 14 18 := vasyuninBEntry_correct_axiom 14 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_14_18_eval :
    ((((11691061/169390000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 18) ∧
    (vasyuninBEntry 14 18 ≤ (((11724939/169390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 9 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G14_19_formula : baezDuarteGramEntry 14 19 = vasyuninBEntry 14 19 := vasyuninBEntry_correct_axiom 14 19 (by norm_num) (by norm_num)

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

theorem G14_20_formula : baezDuarteGramEntry 14 20 = vasyuninBEntry 14 20 := vasyuninBEntry_correct_axiom 14 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_14_20_eval :
    ((((43302617/673830000) : ℚ) : ℝ) ≤ vasyuninBEntry 14 20) ∧
    (vasyuninBEntry 14 20 ≤ (((43437383/673830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 10 2 (by norm_num) (by norm_num) (by norm_num)
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

theorem G15_1_formula : baezDuarteGramEntry 15 1 = vasyuninBEntry 1 15 := by
  rw [baezDuarteGramEntry_symm 15 1]
  exact G1_15_formula

theorem G15_1_interval :
    ((((161452817/971830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 1) ∧
    (baezDuarteGramEntry 15 1 ≤ (((161647183/971830000) : ℚ) : ℝ)) := by
  rw [G15_1_formula]
  exact vasyuninBEntry_1_15_eval

def interval_15_1 : NamedVasyuninInterval :=
{
  h := 15
  k := 1
  lower := (161452817/971830000)
  upper := (161647183/971830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_1_interval
}

theorem G15_2_formula : baezDuarteGramEntry 15 2 = vasyuninBEntry 2 15 := by
  rw [baezDuarteGramEntry_symm 15 2]
  exact G2_15_formula

theorem G15_2_interval :
    ((((8406591/59090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 2) ∧
    (baezDuarteGramEntry 15 2 ≤ (((8418409/59090000) : ℚ) : ℝ)) := by
  rw [G15_2_formula]
  exact vasyuninBEntry_2_15_eval

def interval_15_2 : NamedVasyuninInterval :=
{
  h := 15
  k := 2
  lower := (8406591/59090000)
  upper := (8418409/59090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_2_interval
}

theorem G15_3_formula : baezDuarteGramEntry 15 3 = vasyuninBEntry 3 15 := by
  rw [baezDuarteGramEntry_symm 15 3]
  exact G3_15_formula

theorem G15_3_interval :
    ((((42827239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 3) ∧
    (baezDuarteGramEntry 15 3 ≤ (((42892761/327610000) : ℚ) : ℝ)) := by
  rw [G15_3_formula]
  exact vasyuninBEntry_3_15_eval

def interval_15_3 : NamedVasyuninInterval :=
{
  h := 15
  k := 3
  lower := (42827239/327610000)
  upper := (42892761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_3_interval
}

theorem G15_4_formula : baezDuarteGramEntry 15 4 = vasyuninBEntry 4 15 := by
  rw [baezDuarteGramEntry_symm 15 4]
  exact G4_15_formula

theorem G15_4_interval :
    ((((22107413/185870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 4) ∧
    (baezDuarteGramEntry 15 4 ≤ (((22144587/185870000) : ℚ) : ℝ)) := by
  rw [G15_4_formula]
  exact vasyuninBEntry_4_15_eval

def interval_15_4 : NamedVasyuninInterval :=
{
  h := 15
  k := 4
  lower := (22107413/185870000)
  upper := (22144587/185870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_4_interval
}

theorem G15_5_formula : baezDuarteGramEntry 15 5 = vasyuninBEntry 5 15 := by
  rw [baezDuarteGramEntry_symm 15 5]
  exact G5_15_formula

theorem G15_5_interval :
    ((((107626331/936690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 5) ∧
    (baezDuarteGramEntry 15 5 ≤ (((107813669/936690000) : ℚ) : ℝ)) := by
  rw [G15_5_formula]
  exact vasyuninBEntry_5_15_eval

def interval_15_5 : NamedVasyuninInterval :=
{
  h := 15
  k := 5
  lower := (107626331/936690000)
  upper := (107813669/936690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_5_interval
}

theorem G15_6_formula : baezDuarteGramEntry 15 6 = vasyuninBEntry 6 15 := by
  rw [baezDuarteGramEntry_symm 15 6]
  exact G6_15_formula

theorem G15_6_interval :
    ((((12158461/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 6) ∧
    (baezDuarteGramEntry 15 6 ≤ (((12181539/115390000) : ℚ) : ℝ)) := by
  rw [G15_6_formula]
  exact vasyuninBEntry_6_15_eval

def interval_15_6 : NamedVasyuninInterval :=
{
  h := 15
  k := 6
  lower := (12158461/115390000)
  upper := (12181539/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_6_interval
}

theorem G15_7_formula : baezDuarteGramEntry 15 7 = vasyuninBEntry 7 15 := by
  rw [baezDuarteGramEntry_symm 15 7]
  exact G7_15_formula

theorem G15_7_interval :
    ((((28931421/285790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 7) ∧
    (baezDuarteGramEntry 15 7 ≤ (((28988579/285790000) : ℚ) : ℝ)) := by
  rw [G15_7_formula]
  exact vasyuninBEntry_7_15_eval

def interval_15_7 : NamedVasyuninInterval :=
{
  h := 15
  k := 7
  lower := (28931421/285790000)
  upper := (28988579/285790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_7_interval
}

theorem G15_8_formula : baezDuarteGramEntry 15 8 = vasyuninBEntry 8 15 := by
  rw [baezDuarteGramEntry_symm 15 8]
  exact G8_15_formula

theorem G15_8_interval :
    ((((52665471/545290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 8) ∧
    (baezDuarteGramEntry 15 8 ≤ (((52774529/545290000) : ℚ) : ℝ)) := by
  rw [G15_8_formula]
  exact vasyuninBEntry_8_15_eval

def interval_15_8 : NamedVasyuninInterval :=
{
  h := 15
  k := 8
  lower := (52665471/545290000)
  upper := (52774529/545290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_8_interval
}

theorem G15_9_formula : baezDuarteGramEntry 15 9 = vasyuninBEntry 9 15 := by
  rw [baezDuarteGramEntry_symm 15 9]
  exact G9_15_formula

theorem G15_9_interval :
    ((((80591521/884790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 9) ∧
    (baezDuarteGramEntry 15 9 ≤ (((80768479/884790000) : ℚ) : ℝ)) := by
  rw [G15_9_formula]
  exact vasyuninBEntry_9_15_eval

def interval_15_9 : NamedVasyuninInterval :=
{
  h := 15
  k := 9
  lower := (80591521/884790000)
  upper := (80768479/884790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_9_interval
}

theorem G15_10_formula : baezDuarteGramEntry 15 10 = vasyuninBEntry 10 15 := by
  rw [baezDuarteGramEntry_symm 15 10]
  exact G10_15_formula

theorem G15_10_interval :
    ((((2109169/23935000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 10) ∧
    (baezDuarteGramEntry 15 10 ≤ (((528489/5983750) : ℚ) : ℝ)) := by
  rw [G15_10_formula]
  exact vasyuninBEntry_10_15_eval

def interval_15_10 : NamedVasyuninInterval :=
{
  h := 15
  k := 10
  lower := (2109169/23935000)
  upper := (528489/5983750)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_10_interval
}

theorem G15_11_formula : baezDuarteGramEntry 15 11 = vasyuninBEntry 11 15 := by
  rw [baezDuarteGramEntry_symm 15 11]
  exact G11_15_formula

theorem G15_11_interval :
    ((((130283/1545000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 11) ∧
    (baezDuarteGramEntry 15 11 ≤ (((16324/193125) : ℚ) : ℝ)) := by
  rw [G15_11_formula]
  exact vasyuninBEntry_11_15_eval

def interval_15_11 : NamedVasyuninInterval :=
{
  h := 15
  k := 11
  lower := (130283/1545000)
  upper := (16324/193125)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_11_interval
}

theorem G15_12_formula : baezDuarteGramEntry 15 12 = vasyuninBEntry 12 15 := by
  rw [baezDuarteGramEntry_symm 15 12]
  exact G12_15_formula

theorem G15_12_interval :
    ((((62534071/759290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 12) ∧
    (baezDuarteGramEntry 15 12 ≤ (((62685929/759290000) : ℚ) : ℝ)) := by
  rw [G15_12_formula]
  exact vasyuninBEntry_12_15_eval

def interval_15_12 : NamedVasyuninInterval :=
{
  h := 15
  k := 12
  lower := (62534071/759290000)
  upper := (62685929/759290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_12_interval
}

theorem G15_13_formula : baezDuarteGramEntry 15 13 = vasyuninBEntry 13 15 := by
  rw [baezDuarteGramEntry_symm 15 13]
  exact G13_15_formula

theorem G15_13_interval :
    ((((26002911/320890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 13) ∧
    (baezDuarteGramEntry 15 13 ≤ (((26067089/320890000) : ℚ) : ℝ)) := by
  rw [G15_13_formula]
  exact vasyuninBEntry_13_15_eval

def interval_15_13 : NamedVasyuninInterval :=
{
  h := 15
  k := 13
  lower := (26002911/320890000)
  upper := (26067089/320890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_13_interval
}

theorem G15_14_formula : baezDuarteGramEntry 15 14 = vasyuninBEntry 14 15 := by
  rw [baezDuarteGramEntry_symm 15 14]
  exact G14_15_formula

theorem G15_14_interval :
    ((((49139363/606370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 14) ∧
    (baezDuarteGramEntry 15 14 ≤ (((49260637/606370000) : ℚ) : ℝ)) := by
  rw [G15_14_formula]
  exact vasyuninBEntry_14_15_eval

def interval_15_14 : NamedVasyuninInterval :=
{
  h := 15
  k := 14
  lower := (49139363/606370000)
  upper := (49260637/606370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_14_interval
}

theorem G15_15_formula_eq : baezDuarteGramEntry 15 15 = (1 / (15 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 15 := by norm_num
  rw [baez_duarte_diagonal_scaling 15 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G15_15_log_gamma_interval :
  ((((58560239/697610000) : ℚ) : ℝ) ≤ (1 / (15 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (15 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((58699761/697610000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 15 (by norm_num)
  constructor
  · have : ((((58560239/697610000) : ℚ) : ℝ) ≤ (1 / (15 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (15 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((58699761/697610000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G15_15_interval : ((((58560239/697610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 15) ∧ (baezDuarteGramEntry 15 15 ≤ (((58699761/697610000) : ℚ) : ℝ)) := by
  rw [G15_15_formula_eq]
  exact G15_15_log_gamma_interval

def interval_15_15 : NamedVasyuninInterval :=
{
  h := 15
  k := 15
  lower := (58560239/697610000)
  upper := (58699761/697610000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G15_15_interval
}

theorem G15_16_formula : baezDuarteGramEntry 15 16 = vasyuninBEntry 15 16 := vasyuninBEntry_correct_axiom 15 16 (by norm_num) (by norm_num)

theorem vasyuninBEntry_15_16_eval :
    ((((43632603/573970000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 16) ∧
    (vasyuninBEntry 15 16 ≤ (((43747397/573970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1516_formula_bound
  constructor <;> linarith

theorem G15_16_interval :
    ((((43632603/573970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 16) ∧
    (baezDuarteGramEntry 15 16 ≤ (((43747397/573970000) : ℚ) : ℝ)) := by
  rw [G15_16_formula]
  exact vasyuninBEntry_15_16_eval

def interval_15_16 : NamedVasyuninInterval :=
{
  h := 15
  k := 16
  lower := (43632603/573970000)
  upper := (43747397/573970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_16_interval
}

theorem G15_17_formula : baezDuarteGramEntry 15 17 = vasyuninBEntry 15 17 := vasyuninBEntry_correct_axiom 15 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_15_17_eval :
    ((((29174127/408730000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 17) ∧
    (vasyuninBEntry 15 17 ≤ (((29255873/408730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1517_formula_bound
  constructor <;> linarith

theorem G15_17_interval :
    ((((29174127/408730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 17) ∧
    (baezDuarteGramEntry 15 17 ≤ (((29255873/408730000) : ℚ) : ℝ)) := by
  rw [G15_17_formula]
  exact vasyuninBEntry_15_17_eval

def interval_15_17 : NamedVasyuninInterval :=
{
  h := 15
  k := 17
  lower := (29174127/408730000)
  upper := (29255873/408730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_17_interval
}

theorem G15_18_formula : baezDuarteGramEntry 15 18 = vasyuninBEntry 15 18 := vasyuninBEntry_correct_axiom 15 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_15_18_eval :
    ((((34948577/514230000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 18) ∧
    (vasyuninBEntry 15 18 ≤ (((35051423/514230000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 3 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G15_18_interval :
    ((((34948577/514230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 18) ∧
    (baezDuarteGramEntry 15 18 ≤ (((35051423/514230000) : ℚ) : ℝ)) := by
  rw [G15_18_formula]
  exact vasyuninBEntry_15_18_eval

def interval_15_18 : NamedVasyuninInterval :=
{
  h := 15
  k := 18
  lower := (34948577/514230000)
  upper := (35051423/514230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_18_interval
}

theorem G15_19_formula : baezDuarteGramEntry 15 19 = vasyuninBEntry 15 19 := vasyuninBEntry_correct_axiom 15 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_15_19_eval :
    ((((3683343/56570000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 19) ∧
    (vasyuninBEntry 15 19 ≤ (((3694657/56570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1519_formula_bound
  constructor <;> linarith

theorem G15_19_interval :
    ((((3683343/56570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 19) ∧
    (baezDuarteGramEntry 15 19 ≤ (((3694657/56570000) : ℚ) : ℝ)) := by
  rw [G15_19_formula]
  exact vasyuninBEntry_15_19_eval

def interval_15_19 : NamedVasyuninInterval :=
{
  h := 15
  k := 19
  lower := (3683343/56570000)
  upper := (3694657/56570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_19_interval
}

theorem G15_20_formula : baezDuarteGramEntry 15 20 = vasyuninBEntry 15 20 := vasyuninBEntry_correct_axiom 15 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_15_20_eval :
    ((((2523993/40070000) : ℚ) : ℝ) ≤ vasyuninBEntry 15 20) ∧
    (vasyuninBEntry 15 20 ≤ (((2532007/40070000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 5 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G15_20_interval :
    ((((2523993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 15 20) ∧
    (baezDuarteGramEntry 15 20 ≤ (((2532007/40070000) : ℚ) : ℝ)) := by
  rw [G15_20_formula]
  exact vasyuninBEntry_15_20_eval

def interval_15_20 : NamedVasyuninInterval :=
{
  h := 15
  k := 20
  lower := (2523993/40070000)
  upper := (2532007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G15_20_interval
}

theorem G16_1_formula : baezDuarteGramEntry 16 1 = vasyuninBEntry 1 16 := by
  rw [baezDuarteGramEntry_symm 16 1]
  exact G1_16_formula

theorem G16_1_interval :
    ((((149864983/950170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 1) ∧
    (baezDuarteGramEntry 16 1 ≤ (((150055017/950170000) : ℚ) : ℝ)) := by
  rw [G16_1_formula]
  exact vasyuninBEntry_1_16_eval

def interval_16_1 : NamedVasyuninInterval :=
{
  h := 16
  k := 1
  lower := (149864983/950170000)
  upper := (150055017/950170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_1_interval
}

theorem G16_2_formula : baezDuarteGramEntry 16 2 = vasyuninBEntry 2 16 := by
  rw [baezDuarteGramEntry_symm 16 2]
  exact G2_16_formula

theorem G16_2_interval :
    ((((7473279/54710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 2) ∧
    (baezDuarteGramEntry 16 2 ≤ (((7484221/54710000) : ℚ) : ℝ)) := by
  rw [G16_2_formula]
  exact vasyuninBEntry_2_16_eval

def interval_16_2 : NamedVasyuninInterval :=
{
  h := 16
  k := 2
  lower := (7473279/54710000)
  upper := (7484221/54710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_2_interval
}

theorem G16_3_formula : baezDuarteGramEntry 16 3 = vasyuninBEntry 3 16 := by
  rw [baezDuarteGramEntry_symm 16 3]
  exact G3_16_formula

theorem G16_3_interval :
    ((((19793853/161470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 3) ∧
    (baezDuarteGramEntry 16 3 ≤ (((19826147/161470000) : ℚ) : ℝ)) := by
  rw [G16_3_formula]
  exact vasyuninBEntry_3_16_eval

def interval_16_3 : NamedVasyuninInterval :=
{
  h := 16
  k := 3
  lower := (19793853/161470000)
  upper := (19826147/161470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_3_interval
}

theorem G16_4_formula : baezDuarteGramEntry 16 4 = vasyuninBEntry 4 16 := by
  rw [baezDuarteGramEntry_symm 16 4]
  exact G4_16_formula

theorem G16_4_interval :
    ((((37947287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 4) ∧
    (baezDuarteGramEntry 16 4 ≤ (((38012713/327130000) : ℚ) : ℝ)) := by
  rw [G16_4_formula]
  exact vasyuninBEntry_4_16_eval

def interval_16_4 : NamedVasyuninInterval :=
{
  h := 16
  k := 4
  lower := (37947287/327130000)
  upper := (38012713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_4_interval
}

theorem G16_5_formula : baezDuarteGramEntry 16 5 = vasyuninBEntry 5 16 := by
  rw [baezDuarteGramEntry_symm 16 5]
  exact G5_16_formula

theorem G16_5_interval :
    ((((19049673/178270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 5) ∧
    (baezDuarteGramEntry 16 5 ≤ (((19085327/178270000) : ℚ) : ℝ)) := by
  rw [G16_5_formula]
  exact vasyuninBEntry_5_16_eval

def interval_16_5 : NamedVasyuninInterval :=
{
  h := 16
  k := 5
  lower := (19049673/178270000)
  upper := (19085327/178270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_5_interval
}

theorem G16_6_formula : baezDuarteGramEntry 16 6 = vasyuninBEntry 6 16 := by
  rw [baezDuarteGramEntry_symm 16 6]
  exact G6_16_formula

theorem G16_6_interval :
    ((((4012883/39920000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 6) ∧
    (baezDuarteGramEntry 16 6 ≤ (((4020867/39920000) : ℚ) : ℝ)) := by
  rw [G16_6_formula]
  exact vasyuninBEntry_6_16_eval

def interval_16_6 : NamedVasyuninInterval :=
{
  h := 16
  k := 6
  lower := (4012883/39920000)
  upper := (4020867/39920000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_6_interval
}

theorem G16_7_formula : baezDuarteGramEntry 16 7 = vasyuninBEntry 7 16 := by
  rw [baezDuarteGramEntry_symm 16 7]
  exact G7_16_formula

theorem G16_7_interval :
    ((((1045709/10910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 7) ∧
    (baezDuarteGramEntry 16 7 ≤ (((1047891/10910000) : ℚ) : ℝ)) := by
  rw [G16_7_formula]
  exact vasyuninBEntry_7_16_eval

def interval_16_7 : NamedVasyuninInterval :=
{
  h := 16
  k := 7
  lower := (1045709/10910000)
  upper := (1047891/10910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_7_interval
}

theorem G16_8_formula : baezDuarteGramEntry 16 8 = vasyuninBEntry 8 16 := by
  rw [baezDuarteGramEntry_symm 16 8]
  exact G8_16_formula

theorem G16_8_interval :
    ((((7022717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 8) ∧
    (baezDuarteGramEntry 16 8 ≤ (((7037283/72830000) : ℚ) : ℝ)) := by
  rw [G16_8_formula]
  exact vasyuninBEntry_8_16_eval

def interval_16_8 : NamedVasyuninInterval :=
{
  h := 16
  k := 8
  lower := (7022717/72830000)
  upper := (7037283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_8_interval
}

theorem G16_9_formula : baezDuarteGramEntry 16 9 = vasyuninBEntry 9 16 := by
  rw [baezDuarteGramEntry_symm 16 9]
  exact G9_16_formula

theorem G16_9_interval :
    ((((12042277/137230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 9) ∧
    (baezDuarteGramEntry 16 9 ≤ (((12069723/137230000) : ℚ) : ℝ)) := by
  rw [G16_9_formula]
  exact vasyuninBEntry_9_16_eval

def interval_16_9 : NamedVasyuninInterval :=
{
  h := 16
  k := 9
  lower := (12042277/137230000)
  upper := (12069723/137230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_9_interval
}

theorem G16_10_formula : baezDuarteGramEntry 16 10 = vasyuninBEntry 10 16 := by
  rw [baezDuarteGramEntry_symm 16 10]
  exact G10_16_formula

theorem G16_10_interval :
    ((((1256251/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 10) ∧
    (baezDuarteGramEntry 16 10 ≤ (((1259249/14990000) : ℚ) : ℝ)) := by
  rw [G16_10_formula]
  exact vasyuninBEntry_10_16_eval

def interval_16_10 : NamedVasyuninInterval :=
{
  h := 16
  k := 10
  lower := (1256251/14990000)
  upper := (1259249/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_10_interval
}

theorem G16_11_formula : baezDuarteGramEntry 16 11 = vasyuninBEntry 11 16 := by
  rw [baezDuarteGramEntry_symm 16 11]
  exact G11_16_formula

theorem G16_11_interval :
    ((((21553381/266190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 11) ∧
    (baezDuarteGramEntry 16 11 ≤ (((21606619/266190000) : ℚ) : ℝ)) := by
  rw [G16_11_formula]
  exact vasyuninBEntry_11_16_eval

def interval_16_11 : NamedVasyuninInterval :=
{
  h := 16
  k := 11
  lower := (21553381/266190000)
  upper := (21606619/266190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_11_interval
}

theorem G16_12_formula : baezDuarteGramEntry 16 12 = vasyuninBEntry 12 16 := by
  rw [baezDuarteGramEntry_symm 16 12]
  exact G12_16_formula

theorem G16_12_interval :
    ((((3155993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 12) ∧
    (baezDuarteGramEntry 16 12 ≤ (((3164007/40070000) : ℚ) : ℝ)) := by
  rw [G16_12_formula]
  exact vasyuninBEntry_12_16_eval

def interval_16_12 : NamedVasyuninInterval :=
{
  h := 16
  k := 12
  lower := (3155993/40070000)
  upper := (3164007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_12_interval
}

theorem G16_13_formula : baezDuarteGramEntry 16 13 = vasyuninBEntry 13 16 := by
  rw [baezDuarteGramEntry_symm 16 13]
  exact G13_16_formula

theorem G16_13_interval :
    ((((4146601/53990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 13) ∧
    (baezDuarteGramEntry 16 13 ≤ (((4157399/53990000) : ℚ) : ℝ)) := by
  rw [G16_13_formula]
  exact vasyuninBEntry_13_16_eval

def interval_16_13 : NamedVasyuninInterval :=
{
  h := 16
  k := 13
  lower := (4146601/53990000)
  upper := (4157399/53990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_13_interval
}

theorem G16_14_formula : baezDuarteGramEntry 16 14 = vasyuninBEntry 14 16 := by
  rw [baezDuarteGramEntry_symm 16 14]
  exact G14_16_formula

theorem G16_14_interval :
    ((((55417003/729970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 14) ∧
    (baezDuarteGramEntry 16 14 ≤ (((55562997/729970000) : ℚ) : ℝ)) := by
  rw [G16_14_formula]
  exact vasyuninBEntry_14_16_eval

def interval_16_14 : NamedVasyuninInterval :=
{
  h := 16
  k := 14
  lower := (55417003/729970000)
  upper := (55562997/729970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_14_interval
}

theorem G16_15_formula : baezDuarteGramEntry 16 15 = vasyuninBEntry 15 16 := by
  rw [baezDuarteGramEntry_symm 16 15]
  exact G15_16_formula

theorem G16_15_interval :
    ((((43632603/573970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 15) ∧
    (baezDuarteGramEntry 16 15 ≤ (((43747397/573970000) : ℚ) : ℝ)) := by
  rw [G16_15_formula]
  exact vasyuninBEntry_15_16_eval

def interval_16_15 : NamedVasyuninInterval :=
{
  h := 16
  k := 15
  lower := (43632603/573970000)
  upper := (43747397/573970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_15_interval
}

theorem G16_16_formula_eq : baezDuarteGramEntry 16 16 = (1 / (16 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 16 := by norm_num
  rw [baez_duarte_diagonal_scaling 16 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G16_16_log_gamma_interval :
  ((((24818461/315390000) : ℚ) : ℝ) ≤ (1 / (16 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (16 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((24881539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 16 (by norm_num)
  constructor
  · have : ((((24818461/315390000) : ℚ) : ℝ) ≤ (1 / (16 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (16 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((24881539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G16_16_interval : ((((24818461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 16) ∧ (baezDuarteGramEntry 16 16 ≤ (((24881539/315390000) : ℚ) : ℝ)) := by
  rw [G16_16_formula_eq]
  exact G16_16_log_gamma_interval

def interval_16_16 : NamedVasyuninInterval :=
{
  h := 16
  k := 16
  lower := (24818461/315390000)
  upper := (24881539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G16_16_interval
}

theorem G16_17_formula : baezDuarteGramEntry 16 17 = vasyuninBEntry 16 17 := vasyuninBEntry_correct_axiom 16 17 (by norm_num) (by norm_num)

theorem vasyuninBEntry_16_17_eval :
    ((((36109561/504390000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 17) ∧
    (vasyuninBEntry 16 17 ≤ (((36210439/504390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1617_formula_bound
  constructor <;> linarith

theorem G16_17_interval :
    ((((36109561/504390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 17) ∧
    (baezDuarteGramEntry 16 17 ≤ (((36210439/504390000) : ℚ) : ℝ)) := by
  rw [G16_17_formula]
  exact vasyuninBEntry_16_17_eval

def interval_16_17 : NamedVasyuninInterval :=
{
  h := 16
  k := 17
  lower := (36109561/504390000)
  upper := (36210439/504390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_17_interval
}

theorem G16_18_formula : baezDuarteGramEntry 16 18 = vasyuninBEntry 16 18 := vasyuninBEntry_correct_axiom 16 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_16_18_eval :
    ((((36795403/545970000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 18) ∧
    (vasyuninBEntry 16 18 ≤ (((36904597/545970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 9 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G16_18_interval :
    ((((36795403/545970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 18) ∧
    (baezDuarteGramEntry 16 18 ≤ (((36904597/545970000) : ℚ) : ℝ)) := by
  rw [G16_18_formula]
  exact vasyuninBEntry_16_18_eval

def interval_16_18 : NamedVasyuninInterval :=
{
  h := 16
  k := 18
  lower := (36795403/545970000)
  upper := (36904597/545970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_18_interval
}

theorem G16_19_formula : baezDuarteGramEntry 16 19 = vasyuninBEntry 16 19 := vasyuninBEntry_correct_axiom 16 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_16_19_eval :
    ((((33687533/524670000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 19) ∧
    (vasyuninBEntry 16 19 ≤ (((33792467/524670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1619_formula_bound
  constructor <;> linarith

theorem G16_19_interval :
    ((((33687533/524670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 19) ∧
    (baezDuarteGramEntry 16 19 ≤ (((33792467/524670000) : ℚ) : ℝ)) := by
  rw [G16_19_formula]
  exact vasyuninBEntry_16_19_eval

def interval_16_19 : NamedVasyuninInterval :=
{
  h := 16
  k := 19
  lower := (33687533/524670000)
  upper := (33792467/524670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_19_interval
}

theorem G16_20_formula : baezDuarteGramEntry 16 20 = vasyuninBEntry 16 20 := vasyuninBEntry_correct_axiom 16 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_16_20_eval :
    ((((21470227/347730000) : ℚ) : ℝ) ≤ vasyuninBEntry 16 20) ∧
    (vasyuninBEntry 16 20 ≤ (((21539773/347730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 4 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G16_20_interval :
    ((((21470227/347730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 16 20) ∧
    (baezDuarteGramEntry 16 20 ≤ (((21539773/347730000) : ℚ) : ℝ)) := by
  rw [G16_20_formula]
  exact vasyuninBEntry_16_20_eval

def interval_16_20 : NamedVasyuninInterval :=
{
  h := 16
  k := 20
  lower := (21470227/347730000)
  upper := (21539773/347730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G16_20_interval
}

theorem G17_1_formula : baezDuarteGramEntry 17 1 = vasyuninBEntry 1 17 := by
  rw [baezDuarteGramEntry_symm 17 1]
  exact G1_17_formula

theorem G17_1_interval :
    ((((149910189/998110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 1) ∧
    (baezDuarteGramEntry 17 1 ≤ (((150109811/998110000) : ℚ) : ℝ)) := by
  rw [G17_1_formula]
  exact vasyuninBEntry_1_17_eval

def interval_17_1 : NamedVasyuninInterval :=
{
  h := 17
  k := 1
  lower := (149910189/998110000)
  upper := (150109811/998110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_1_interval
}

theorem G17_2_formula : baezDuarteGramEntry 17 2 = vasyuninBEntry 2 17 := by
  rw [baezDuarteGramEntry_symm 17 2]
  exact G2_17_formula

theorem G17_2_interval :
    ((((856697/6630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 2) ∧
    (baezDuarteGramEntry 17 2 ≤ (((858023/6630000) : ℚ) : ℝ)) := by
  rw [G17_2_formula]
  exact vasyuninBEntry_2_17_eval

def interval_17_2 : NamedVasyuninInterval :=
{
  h := 17
  k := 2
  lower := (856697/6630000)
  upper := (858023/6630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_2_interval
}

theorem G17_3_formula : baezDuarteGramEntry 17 3 = vasyuninBEntry 3 17 := by
  rw [baezDuarteGramEntry_symm 17 3]
  exact G3_17_formula

theorem G17_3_interval :
    ((((6694909/57160000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 3) ∧
    (baezDuarteGramEntry 17 3 ≤ (((6706341/57160000) : ℚ) : ℝ)) := by
  rw [G17_3_formula]
  exact vasyuninBEntry_3_17_eval

def interval_17_3 : NamedVasyuninInterval :=
{
  h := 17
  k := 3
  lower := (6694909/57160000)
  upper := (6706341/57160000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_3_interval
}

theorem G17_4_formula : baezDuarteGramEntry 17 4 = vasyuninBEntry 4 17 := by
  rw [baezDuarteGramEntry_symm 17 4]
  exact G4_17_formula

theorem G17_4_interval :
    ((((3296469/30310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 4) ∧
    (baezDuarteGramEntry 17 4 ≤ (((3302531/30310000) : ℚ) : ℝ)) := by
  rw [G17_4_formula]
  exact vasyuninBEntry_4_17_eval

def interval_17_4 : NamedVasyuninInterval :=
{
  h := 17
  k := 4
  lower := (3296469/30310000)
  upper := (3302531/30310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_4_interval
}

theorem G17_5_formula : baezDuarteGramEntry 17 5 = vasyuninBEntry 5 17 := by
  rw [baezDuarteGramEntry_symm 17 5]
  exact G5_17_formula

theorem G17_5_interval :
    ((((43667113/428870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 5) ∧
    (baezDuarteGramEntry 17 5 ≤ (((43752887/428870000) : ℚ) : ℝ)) := by
  rw [G17_5_formula]
  exact vasyuninBEntry_5_17_eval

def interval_17_5 : NamedVasyuninInterval :=
{
  h := 17
  k := 5
  lower := (43667113/428870000)
  upper := (43752887/428870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_5_interval
}

theorem G17_6_formula : baezDuarteGramEntry 17 6 = vasyuninBEntry 6 17 := by
  rw [baezDuarteGramEntry_symm 17 6]
  exact G6_17_formula

theorem G17_6_interval :
    ((((79068453/815470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 6) ∧
    (baezDuarteGramEntry 17 6 ≤ (((79231547/815470000) : ℚ) : ℝ)) := by
  rw [G17_6_formula]
  exact vasyuninBEntry_6_17_eval

def interval_17_6 : NamedVasyuninInterval :=
{
  h := 17
  k := 6
  lower := (79068453/815470000)
  upper := (79231547/815470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_6_interval
}

theorem G17_7_formula : baezDuarteGramEntry 17 7 = vasyuninBEntry 7 17 := by
  rw [baezDuarteGramEntry_symm 17 7]
  exact G7_17_formula

theorem G17_7_interval :
    ((((41439803/451970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 7) ∧
    (baezDuarteGramEntry 17 7 ≤ (((41530197/451970000) : ℚ) : ℝ)) := by
  rw [G17_7_formula]
  exact vasyuninBEntry_7_17_eval

def interval_17_7 : NamedVasyuninInterval :=
{
  h := 17
  k := 7
  lower := (41439803/451970000)
  upper := (41530197/451970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_7_interval
}

theorem G17_8_formula : baezDuarteGramEntry 17 8 = vasyuninBEntry 8 17 := by
  rw [baezDuarteGramEntry_symm 17 8]
  exact G8_17_formula

theorem G17_8_interval :
    ((((10578151/118490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 8) ∧
    (baezDuarteGramEntry 17 8 ≤ (((10601849/118490000) : ℚ) : ℝ)) := by
  rw [G17_8_formula]
  exact vasyuninBEntry_8_17_eval

def interval_17_8 : NamedVasyuninInterval :=
{
  h := 17
  k := 8
  lower := (10578151/118490000)
  upper := (10601849/118490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_8_interval
}

theorem G17_9_formula : baezDuarteGramEntry 17 9 = vasyuninBEntry 9 17 := by
  rw [baezDuarteGramEntry_symm 17 9]
  exact G9_17_formula

theorem G17_9_interval :
    ((((25929723/302770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 9) ∧
    (baezDuarteGramEntry 17 9 ≤ (((25990277/302770000) : ℚ) : ℝ)) := by
  rw [G17_9_formula]
  exact vasyuninBEntry_9_17_eval

def interval_17_9 : NamedVasyuninInterval :=
{
  h := 17
  k := 9
  lower := (25929723/302770000)
  upper := (25990277/302770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_9_interval
}

theorem G17_10_formula : baezDuarteGramEntry 17 10 = vasyuninBEntry 10 17 := by
  rw [baezDuarteGramEntry_symm 17 10]
  exact G10_17_formula

theorem G17_10_interval :
    ((((35975501/444990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 10) ∧
    (baezDuarteGramEntry 17 10 ≤ (((36064499/444990000) : ℚ) : ℝ)) := by
  rw [G17_10_formula]
  exact vasyuninBEntry_10_17_eval

def interval_17_10 : NamedVasyuninInterval :=
{
  h := 17
  k := 10
  lower := (35975501/444990000)
  upper := (36064499/444990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_10_interval
}

theorem G17_11_formula : baezDuarteGramEntry 17 11 = vasyuninBEntry 11 17 := by
  rw [baezDuarteGramEntry_symm 17 11]
  exact G11_17_formula

theorem G17_11_interval :
    ((((3587397/46030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 11) ∧
    (baezDuarteGramEntry 17 11 ≤ (((3596603/46030000) : ℚ) : ℝ)) := by
  rw [G17_11_formula]
  exact vasyuninBEntry_11_17_eval

def interval_17_11 : NamedVasyuninInterval :=
{
  h := 17
  k := 11
  lower := (3587397/46030000)
  upper := (3596603/46030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_11_interval
}

theorem G17_12_formula : baezDuarteGramEntry 17 12 = vasyuninBEntry 12 17 := by
  rw [baezDuarteGramEntry_symm 17 12]
  exact G12_17_formula

theorem G17_12_interval :
    ((((12688163/168370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 12) ∧
    (baezDuarteGramEntry 17 12 ≤ (((12721837/168370000) : ℚ) : ℝ)) := by
  rw [G17_12_formula]
  exact vasyuninBEntry_12_17_eval

def interval_17_12 : NamedVasyuninInterval :=
{
  h := 17
  k := 12
  lower := (12688163/168370000)
  upper := (12721837/168370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_12_interval
}

theorem G17_13_formula : baezDuarteGramEntry 17 13 = vasyuninBEntry 13 17 := by
  rw [baezDuarteGramEntry_symm 17 13]
  exact G13_17_formula

theorem G17_13_interval :
    ((((22654157/308430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 13) ∧
    (baezDuarteGramEntry 17 13 ≤ (((22715843/308430000) : ℚ) : ℝ)) := by
  rw [G17_13_formula]
  exact vasyuninBEntry_13_17_eval

def interval_17_13 : NamedVasyuninInterval :=
{
  h := 17
  k := 13
  lower := (22654157/308430000)
  upper := (22715843/308430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_13_interval
}

theorem G17_14_formula : baezDuarteGramEntry 17 14 = vasyuninBEntry 14 17 := by
  rw [baezDuarteGramEntry_symm 17 14]
  exact G14_17_formula

theorem G17_14_interval :
    ((((552753/7670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 14) ∧
    (baezDuarteGramEntry 17 14 ≤ (((554287/7670000) : ℚ) : ℝ)) := by
  rw [G17_14_formula]
  exact vasyuninBEntry_14_17_eval

def interval_17_14 : NamedVasyuninInterval :=
{
  h := 17
  k := 14
  lower := (552753/7670000)
  upper := (554287/7670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_14_interval
}

theorem G17_15_formula : baezDuarteGramEntry 17 15 = vasyuninBEntry 15 17 := by
  rw [baezDuarteGramEntry_symm 17 15]
  exact G15_17_formula

theorem G17_15_interval :
    ((((29174127/408730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 15) ∧
    (baezDuarteGramEntry 17 15 ≤ (((29255873/408730000) : ℚ) : ℝ)) := by
  rw [G17_15_formula]
  exact vasyuninBEntry_15_17_eval

def interval_17_15 : NamedVasyuninInterval :=
{
  h := 17
  k := 15
  lower := (29174127/408730000)
  upper := (29255873/408730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_15_interval
}

theorem G17_16_formula : baezDuarteGramEntry 17 16 = vasyuninBEntry 16 17 := by
  rw [baezDuarteGramEntry_symm 17 16]
  exact G16_17_formula

theorem G17_16_interval :
    ((((36109561/504390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 16) ∧
    (baezDuarteGramEntry 17 16 ≤ (((36210439/504390000) : ℚ) : ℝ)) := by
  rw [G17_16_formula]
  exact vasyuninBEntry_16_17_eval

def interval_17_16 : NamedVasyuninInterval :=
{
  h := 17
  k := 16
  lower := (36109561/504390000)
  upper := (36210439/504390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_16_interval
}

theorem G17_17_formula_eq : baezDuarteGramEntry 17 17 = (1 / (17 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 17 := by norm_num
  rw [baez_duarte_diagonal_scaling 17 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G17_17_log_gamma_interval :
  ((((6651019/89810000) : ℚ) : ℝ) ≤ (1 / (17 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (17 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((6668981/89810000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 17 (by norm_num)
  constructor
  · have : ((((6651019/89810000) : ℚ) : ℝ) ≤ (1 / (17 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (17 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((6668981/89810000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G17_17_interval : ((((6651019/89810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 17) ∧ (baezDuarteGramEntry 17 17 ≤ (((6668981/89810000) : ℚ) : ℝ)) := by
  rw [G17_17_formula_eq]
  exact G17_17_log_gamma_interval

def interval_17_17 : NamedVasyuninInterval :=
{
  h := 17
  k := 17
  lower := (6651019/89810000)
  upper := (6668981/89810000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G17_17_interval
}

theorem G17_18_formula : baezDuarteGramEntry 17 18 = vasyuninBEntry 17 18 := vasyuninBEntry_correct_axiom 17 18 (by norm_num) (by norm_num)

theorem vasyuninBEntry_17_18_eval :
    ((((40150653/593470000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 18) ∧
    (vasyuninBEntry 17 18 ≤ (((40269347/593470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1718_formula_bound
  constructor <;> linarith

theorem G17_18_interval :
    ((((40150653/593470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 18) ∧
    (baezDuarteGramEntry 17 18 ≤ (((40269347/593470000) : ℚ) : ℝ)) := by
  rw [G17_18_formula]
  exact vasyuninBEntry_17_18_eval

def interval_17_18 : NamedVasyuninInterval :=
{
  h := 17
  k := 18
  lower := (40150653/593470000)
  upper := (40269347/593470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_18_interval
}

theorem G17_19_formula : baezDuarteGramEntry 17 19 = vasyuninBEntry 17 19 := vasyuninBEntry_correct_axiom 17 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_17_19_eval :
    ((((9257493/145070000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 19) ∧
    (vasyuninBEntry 17 19 ≤ (((9286507/145070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1719_formula_bound
  constructor <;> linarith

theorem G17_19_interval :
    ((((9257493/145070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 19) ∧
    (baezDuarteGramEntry 17 19 ≤ (((9286507/145070000) : ℚ) : ℝ)) := by
  rw [G17_19_formula]
  exact vasyuninBEntry_17_19_eval

def interval_17_19 : NamedVasyuninInterval :=
{
  h := 17
  k := 19
  lower := (9257493/145070000)
  upper := (9286507/145070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_19_interval
}

theorem G17_20_formula : baezDuarteGramEntry 17 20 = vasyuninBEntry 17 20 := vasyuninBEntry_correct_axiom 17 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_17_20_eval :
    ((((43069279/707210000) : ℚ) : ℝ) ≤ vasyuninBEntry 17 20) ∧
    (vasyuninBEntry 17 20 ≤ (((43210721/707210000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1720_formula_bound
  constructor <;> linarith

theorem G17_20_interval :
    ((((43069279/707210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 17 20) ∧
    (baezDuarteGramEntry 17 20 ≤ (((43210721/707210000) : ℚ) : ℝ)) := by
  rw [G17_20_formula]
  exact vasyuninBEntry_17_20_eval

def interval_17_20 : NamedVasyuninInterval :=
{
  h := 17
  k := 20
  lower := (43069279/707210000)
  upper := (43210721/707210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G17_20_interval
}

theorem G18_1_formula : baezDuarteGramEntry 18 1 = vasyuninBEntry 1 18 := by
  rw [baezDuarteGramEntry_symm 18 1]
  exact G1_18_formula

theorem G18_1_interval :
    ((((65389403/455970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 1) ∧
    (baezDuarteGramEntry 18 1 ≤ (((65480597/455970000) : ℚ) : ℝ)) := by
  rw [G18_1_formula]
  exact vasyuninBEntry_1_18_eval

def interval_18_1 : NamedVasyuninInterval :=
{
  h := 18
  k := 1
  lower := (65389403/455970000)
  upper := (65480597/455970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_1_interval
}

theorem G18_2_formula : baezDuarteGramEntry 18 2 = vasyuninBEntry 2 18 := by
  rw [baezDuarteGramEntry_symm 18 2]
  exact G2_18_formula

theorem G18_2_interval :
    ((((40807243/327570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 2) ∧
    (baezDuarteGramEntry 18 2 ≤ (((40872757/327570000) : ℚ) : ℝ)) := by
  rw [G18_2_formula]
  exact vasyuninBEntry_2_18_eval

def interval_18_2 : NamedVasyuninInterval :=
{
  h := 18
  k := 2
  lower := (40807243/327570000)
  upper := (40872757/327570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_2_interval
}

theorem G18_3_formula : baezDuarteGramEntry 18 3 = vasyuninBEntry 3 18 := by
  rw [baezDuarteGramEntry_symm 18 3]
  exact G3_18_formula

theorem G18_3_interval :
    ((((9472921/83290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 3) ∧
    (baezDuarteGramEntry 18 3 ≤ (((9489579/83290000) : ℚ) : ℝ)) := by
  rw [G18_3_formula]
  exact vasyuninBEntry_3_18_eval

def interval_18_3 : NamedVasyuninInterval :=
{
  h := 18
  k := 3
  lower := (9472921/83290000)
  upper := (9489579/83290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_3_interval
}

theorem G18_4_formula : baezDuarteGramEntry 18 4 = vasyuninBEntry 4 18 := by
  rw [baezDuarteGramEntry_symm 18 4]
  exact G4_18_formula

theorem G18_4_interval :
    ((((52819343/506570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 4) ∧
    (baezDuarteGramEntry 18 4 ≤ (((52920657/506570000) : ℚ) : ℝ)) := by
  rw [G18_4_formula]
  exact vasyuninBEntry_4_18_eval

def interval_18_4 : NamedVasyuninInterval :=
{
  h := 18
  k := 4
  lower := (52819343/506570000)
  upper := (52920657/506570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_4_interval
}

theorem G18_5_formula : baezDuarteGramEntry 18 5 = vasyuninBEntry 5 18 := by
  rw [baezDuarteGramEntry_symm 18 5]
  exact G5_18_formula

theorem G18_5_interval :
    ((((24899519/254810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 5) ∧
    (baezDuarteGramEntry 18 5 ≤ (((24950481/254810000) : ℚ) : ℝ)) := by
  rw [G18_5_formula]
  exact vasyuninBEntry_5_18_eval

def interval_18_5 : NamedVasyuninInterval :=
{
  h := 18
  k := 5
  lower := (24899519/254810000)
  upper := (24950481/254810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_5_interval
}

theorem G18_6_formula : baezDuarteGramEntry 18 6 = vasyuninBEntry 6 18 := by
  rw [baezDuarteGramEntry_symm 18 6]
  exact G6_18_formula

theorem G18_6_interval :
    ((((48279569/504310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 6) ∧
    (baezDuarteGramEntry 18 6 ≤ (((48380431/504310000) : ℚ) : ℝ)) := by
  rw [G18_6_formula]
  exact vasyuninBEntry_6_18_eval

def interval_18_6 : NamedVasyuninInterval :=
{
  h := 18
  k := 6
  lower := (48279569/504310000)
  upper := (48380431/504310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_6_interval
}

theorem G18_7_formula : baezDuarteGramEntry 18 7 = vasyuninBEntry 7 18 := by
  rw [baezDuarteGramEntry_symm 18 7]
  exact G7_18_formula

theorem G18_7_interval :
    ((((42916311/486890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 7) ∧
    (baezDuarteGramEntry 18 7 ≤ (((43013689/486890000) : ℚ) : ℝ)) := by
  rw [G18_7_formula]
  exact vasyuninBEntry_7_18_eval

def interval_18_7 : NamedVasyuninInterval :=
{
  h := 18
  k := 7
  lower := (42916311/486890000)
  upper := (43013689/486890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_7_interval
}

theorem G18_8_formula : baezDuarteGramEntry 18 8 = vasyuninBEntry 8 18 := by
  rw [baezDuarteGramEntry_symm 18 8]
  exact G8_18_formula

theorem G18_8_interval :
    ((((81474103/958970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 8) ∧
    (baezDuarteGramEntry 18 8 ≤ (((81665897/958970000) : ℚ) : ℝ)) := by
  rw [G18_8_formula]
  exact vasyuninBEntry_8_18_eval

def interval_18_8 : NamedVasyuninInterval :=
{
  h := 18
  k := 8
  lower := (81474103/958970000)
  upper := (81665897/958970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_8_interval
}

theorem G18_9_formula : baezDuarteGramEntry 18 9 = vasyuninBEntry 9 18 := by
  rw [baezDuarteGramEntry_symm 18 9]
  exact G9_18_formula

theorem G18_9_interval :
    ((((37825863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 9) ∧
    (baezDuarteGramEntry 18 9 ≤ (((37914137/441370000) : ℚ) : ℝ)) := by
  rw [G18_9_formula]
  exact vasyuninBEntry_9_18_eval

def interval_18_9 : NamedVasyuninInterval :=
{
  h := 18
  k := 9
  lower := (37825863/441370000)
  upper := (37914137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_9_interval
}

theorem G18_10_formula : baezDuarteGramEntry 18 10 = vasyuninBEntry 10 18 := by
  rw [baezDuarteGramEntry_symm 18 10]
  exact G10_18_formula

theorem G18_10_interval :
    ((((8609039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 10) ∧
    (baezDuarteGramEntry 18 10 ≤ (((8630961/109610000) : ℚ) : ℝ)) := by
  rw [G18_10_formula]
  exact vasyuninBEntry_10_18_eval

def interval_18_10 : NamedVasyuninInterval :=
{
  h := 18
  k := 10
  lower := (8609039/109610000)
  upper := (8630961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_10_interval
}

theorem G18_11_formula : baezDuarteGramEntry 18 11 = vasyuninBEntry 11 18 := by
  rw [baezDuarteGramEntry_symm 18 11]
  exact G11_18_formula

theorem G18_11_interval :
    ((((32107257/427430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 11) ∧
    (baezDuarteGramEntry 18 11 ≤ (((32192743/427430000) : ℚ) : ℝ)) := by
  rw [G18_11_formula]
  exact vasyuninBEntry_11_18_eval

def interval_18_11 : NamedVasyuninInterval :=
{
  h := 18
  k := 11
  lower := (32107257/427430000)
  upper := (32192743/427430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_11_interval
}

theorem G18_12_formula : baezDuarteGramEntry 18 12 = vasyuninBEntry 12 18 := by
  rw [baezDuarteGramEntry_symm 18 12]
  exact G12_18_formula

theorem G18_12_interval :
    ((((9766697/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 12) ∧
    (baezDuarteGramEntry 18 12 ≤ (((9793303/133030000) : ℚ) : ℝ)) := by
  rw [G18_12_formula]
  exact vasyuninBEntry_12_18_eval

def interval_18_12 : NamedVasyuninInterval :=
{
  h := 18
  k := 12
  lower := (9766697/133030000)
  upper := (9793303/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_12_interval
}

theorem G18_13_formula : baezDuarteGramEntry 18 13 = vasyuninBEntry 13 18 := by
  rw [baezDuarteGramEntry_symm 18 13]
  exact G13_18_formula

theorem G18_13_interval :
    ((((27021719/382810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 13) ∧
    (baezDuarteGramEntry 18 13 ≤ (((27098281/382810000) : ℚ) : ℝ)) := by
  rw [G18_13_formula]
  exact vasyuninBEntry_13_18_eval

def interval_18_13 : NamedVasyuninInterval :=
{
  h := 18
  k := 13
  lower := (27021719/382810000)
  upper := (27098281/382810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_13_interval
}

theorem G18_14_formula : baezDuarteGramEntry 18 14 = vasyuninBEntry 14 18 := by
  rw [baezDuarteGramEntry_symm 18 14]
  exact G14_18_formula

theorem G18_14_interval :
    ((((11691061/169390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 14) ∧
    (baezDuarteGramEntry 18 14 ≤ (((11724939/169390000) : ℚ) : ℝ)) := by
  rw [G18_14_formula]
  exact vasyuninBEntry_14_18_eval

def interval_18_14 : NamedVasyuninInterval :=
{
  h := 18
  k := 14
  lower := (11691061/169390000)
  upper := (11724939/169390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_14_interval
}

theorem G18_15_formula : baezDuarteGramEntry 18 15 = vasyuninBEntry 15 18 := by
  rw [baezDuarteGramEntry_symm 18 15]
  exact G15_18_formula

theorem G18_15_interval :
    ((((34948577/514230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 15) ∧
    (baezDuarteGramEntry 18 15 ≤ (((35051423/514230000) : ℚ) : ℝ)) := by
  rw [G18_15_formula]
  exact vasyuninBEntry_15_18_eval

def interval_18_15 : NamedVasyuninInterval :=
{
  h := 18
  k := 15
  lower := (34948577/514230000)
  upper := (35051423/514230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_15_interval
}

theorem G18_16_formula : baezDuarteGramEntry 18 16 = vasyuninBEntry 16 18 := by
  rw [baezDuarteGramEntry_symm 18 16]
  exact G16_18_formula

theorem G18_16_interval :
    ((((36795403/545970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 16) ∧
    (baezDuarteGramEntry 18 16 ≤ (((36904597/545970000) : ℚ) : ℝ)) := by
  rw [G18_16_formula]
  exact vasyuninBEntry_16_18_eval

def interval_18_16 : NamedVasyuninInterval :=
{
  h := 18
  k := 16
  lower := (36795403/545970000)
  upper := (36904597/545970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_16_interval
}

theorem G18_17_formula : baezDuarteGramEntry 18 17 = vasyuninBEntry 17 18 := by
  rw [baezDuarteGramEntry_symm 18 17]
  exact G17_18_formula

theorem G18_17_interval :
    ((((40150653/593470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 17) ∧
    (baezDuarteGramEntry 18 17 ≤ (((40269347/593470000) : ℚ) : ℝ)) := by
  rw [G18_17_formula]
  exact vasyuninBEntry_17_18_eval

def interval_18_17 : NamedVasyuninInterval :=
{
  h := 18
  k := 17
  lower := (40150653/593470000)
  upper := (40269347/593470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_17_interval
}

theorem G18_18_formula_eq : baezDuarteGramEntry 18 18 = (1 / (18 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 18 := by norm_num
  rw [baez_duarte_diagonal_scaling 18 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G18_18_log_gamma_interval :
  ((((6281019/89810000) : ℚ) : ℝ) ≤ (1 / (18 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (18 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((6298981/89810000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 18 (by norm_num)
  constructor
  · have : ((((6281019/89810000) : ℚ) : ℝ) ≤ (1 / (18 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (18 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((6298981/89810000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G18_18_interval : ((((6281019/89810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 18) ∧ (baezDuarteGramEntry 18 18 ≤ (((6298981/89810000) : ℚ) : ℝ)) := by
  rw [G18_18_formula_eq]
  exact G18_18_log_gamma_interval

def interval_18_18 : NamedVasyuninInterval :=
{
  h := 18
  k := 18
  lower := (6281019/89810000)
  upper := (6298981/89810000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G18_18_interval
}

theorem G18_19_formula : baezDuarteGramEntry 18 19 = vasyuninBEntry 18 19 := vasyuninBEntry_correct_axiom 18 19 (by norm_num) (by norm_num)

theorem vasyuninBEntry_18_19_eval :
    ((((30397601/473990000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 19) ∧
    (vasyuninBEntry 18 19 ≤ (((30492399/473990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1819_formula_bound
  constructor <;> linarith

theorem G18_19_interval :
    ((((30397601/473990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 19) ∧
    (baezDuarteGramEntry 18 19 ≤ (((30492399/473990000) : ℚ) : ℝ)) := by
  rw [G18_19_formula]
  exact vasyuninBEntry_18_19_eval

def interval_18_19 : NamedVasyuninInterval :=
{
  h := 18
  k := 19
  lower := (30397601/473990000)
  upper := (30492399/473990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_19_interval
}

theorem G18_20_formula : baezDuarteGramEntry 18 20 = vasyuninBEntry 18 20 := vasyuninBEntry_correct_axiom 18 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_18_20_eval :
    ((((44356831/731690000) : ℚ) : ℝ) ≤ vasyuninBEntry 18 20) ∧
    (vasyuninBEntry 18 20 ≤ (((44503169/731690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_9_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 9 10 2 (by norm_num) (by norm_num) (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G18_20_interval :
    ((((44356831/731690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 18 20) ∧
    (baezDuarteGramEntry 18 20 ≤ (((44503169/731690000) : ℚ) : ℝ)) := by
  rw [G18_20_formula]
  exact vasyuninBEntry_18_20_eval

def interval_18_20 : NamedVasyuninInterval :=
{
  h := 18
  k := 20
  lower := (44356831/731690000)
  upper := (44503169/731690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G18_20_interval
}

theorem G19_1_formula : baezDuarteGramEntry 19 1 = vasyuninBEntry 1 19 := by
  rw [baezDuarteGramEntry_symm 19 1]
  exact G1_19_formula

theorem G19_1_interval :
    ((((2263351/16490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 1) ∧
    (baezDuarteGramEntry 19 1 ≤ (((2266649/16490000) : ℚ) : ℝ)) := by
  rw [G19_1_formula]
  exact vasyuninBEntry_1_19_eval

def interval_19_1 : NamedVasyuninInterval :=
{
  h := 19
  k := 1
  lower := (2263351/16490000)
  upper := (2266649/16490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_1_interval
}

theorem G19_2_formula : baezDuarteGramEntry 19 2 = vasyuninBEntry 2 19 := by
  rw [baezDuarteGramEntry_symm 19 2]
  exact G2_19_formula

theorem G19_2_interval :
    ((((37213607/313930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 2) ∧
    (baezDuarteGramEntry 19 2 ≤ (((37276393/313930000) : ℚ) : ℝ)) := by
  rw [G19_2_formula]
  exact vasyuninBEntry_2_19_eval

def interval_19_2 : NamedVasyuninInterval :=
{
  h := 19
  k := 2
  lower := (37213607/313930000)
  upper := (37276393/313930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_2_interval
}

theorem G19_3_formula : baezDuarteGramEntry 19 3 = vasyuninBEntry 3 19 := by
  rw [baezDuarteGramEntry_symm 19 3]
  exact G3_19_formula

theorem G19_3_interval :
    ((((9353321/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 3) ∧
    (baezDuarteGramEntry 19 3 ≤ (((9370679/86790000) : ℚ) : ℝ)) := by
  rw [G19_3_formula]
  exact vasyuninBEntry_3_19_eval

def interval_19_3 : NamedVasyuninInterval :=
{
  h := 19
  k := 3
  lower := (9353321/86790000)
  upper := (9370679/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_3_interval
}

theorem G19_4_formula : baezDuarteGramEntry 19 4 = vasyuninBEntry 4 19 := by
  rw [baezDuarteGramEntry_symm 19 4]
  exact G4_19_formula

theorem G19_4_interval :
    ((((13139383/131170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 4) ∧
    (baezDuarteGramEntry 19 4 ≤ (((13165617/131170000) : ℚ) : ℝ)) := by
  rw [G19_4_formula]
  exact vasyuninBEntry_4_19_eval

def interval_19_4 : NamedVasyuninInterval :=
{
  h := 19
  k := 4
  lower := (13139383/131170000)
  upper := (13165617/131170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_4_interval
}

theorem G19_5_formula : baezDuarteGramEntry 19 5 = vasyuninBEntry 5 19 := by
  rw [baezDuarteGramEntry_symm 19 5]
  exact G5_19_formula

theorem G19_5_interval :
    ((((37759987/400130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 5) ∧
    (baezDuarteGramEntry 19 5 ≤ (((37840013/400130000) : ℚ) : ℝ)) := by
  rw [G19_5_formula]
  exact vasyuninBEntry_5_19_eval

def interval_19_5 : NamedVasyuninInterval :=
{
  h := 19
  k := 5
  lower := (37759987/400130000)
  upper := (37840013/400130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_5_interval
}

theorem G19_6_formula : baezDuarteGramEntry 19 6 = vasyuninBEntry 6 19 := by
  rw [baezDuarteGramEntry_symm 19 6]
  exact G6_19_formula

theorem G19_6_interval :
    ((((16491647/183530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 6) ∧
    (baezDuarteGramEntry 19 6 ≤ (((16528353/183530000) : ℚ) : ℝ)) := by
  rw [G19_6_formula]
  exact vasyuninBEntry_6_19_eval

def interval_19_6 : NamedVasyuninInterval :=
{
  h := 19
  k := 6
  lower := (16491647/183530000)
  upper := (16528353/183530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_6_interval
}

theorem G19_7_formula : baezDuarteGramEntry 19 7 = vasyuninBEntry 7 19 := by
  rw [baezDuarteGramEntry_symm 19 7]
  exact G7_19_formula

theorem G19_7_interval :
    ((((2231877/26230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 7) ∧
    (baezDuarteGramEntry 19 7 ≤ (((2237123/26230000) : ℚ) : ℝ)) := by
  rw [G19_7_formula]
  exact vasyuninBEntry_7_19_eval

def interval_19_7 : NamedVasyuninInterval :=
{
  h := 19
  k := 7
  lower := (2231877/26230000)
  upper := (2237123/26230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_7_interval
}

theorem G19_8_formula : baezDuarteGramEntry 19 8 = vasyuninBEntry 8 19 := by
  rw [baezDuarteGramEntry_symm 19 8]
  exact G8_19_formula

theorem G19_8_interval :
    ((((36585097/449030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 8) ∧
    (baezDuarteGramEntry 19 8 ≤ (((36674903/449030000) : ℚ) : ℝ)) := by
  rw [G19_8_formula]
  exact vasyuninBEntry_8_19_eval

def interval_19_8 : NamedVasyuninInterval :=
{
  h := 19
  k := 8
  lower := (36585097/449030000)
  upper := (36674903/449030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_8_interval
}

theorem G19_9_formula : baezDuarteGramEntry 19 9 = vasyuninBEntry 9 19 := by
  rw [baezDuarteGramEntry_symm 19 9]
  exact G9_19_formula

theorem G19_9_interval :
    ((((25068609/313910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 9) ∧
    (baezDuarteGramEntry 19 9 ≤ (((25131391/313910000) : ℚ) : ℝ)) := by
  rw [G19_9_formula]
  exact vasyuninBEntry_9_19_eval

def interval_19_9 : NamedVasyuninInterval :=
{
  h := 19
  k := 9
  lower := (25068609/313910000)
  upper := (25131391/313910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_9_interval
}

theorem G19_10_formula : baezDuarteGramEntry 19 10 = vasyuninBEntry 10 19 := by
  rw [baezDuarteGramEntry_symm 19 10]
  exact G10_19_formula

theorem G19_10_interval :
    ((((12617601/163990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 10) ∧
    (baezDuarteGramEntry 19 10 ≤ (((12650399/163990000) : ℚ) : ℝ)) := by
  rw [G19_10_formula]
  exact vasyuninBEntry_10_19_eval

def interval_19_10 : NamedVasyuninInterval :=
{
  h := 19
  k := 10
  lower := (12617601/163990000)
  upper := (12650399/163990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_10_interval
}

theorem G19_11_formula : baezDuarteGramEntry 19 11 = vasyuninBEntry 11 19 := by
  rw [baezDuarteGramEntry_symm 19 11]
  exact G11_19_formula

theorem G19_11_interval :
    ((((1617779/22210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 11) ∧
    (baezDuarteGramEntry 19 11 ≤ (((1622221/22210000) : ℚ) : ℝ)) := by
  rw [G19_11_formula]
  exact vasyuninBEntry_11_19_eval

def interval_19_11 : NamedVasyuninInterval :=
{
  h := 19
  k := 11
  lower := (1617779/22210000)
  upper := (1622221/22210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_11_interval
}

theorem G19_12_formula : baezDuarteGramEntry 19 12 = vasyuninBEntry 12 19 := by
  rw [baezDuarteGramEntry_symm 19 12]
  exact G12_19_formula

theorem G19_12_interval :
    ((((2970771/42290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 12) ∧
    (baezDuarteGramEntry 19 12 ≤ (((2979229/42290000) : ℚ) : ℝ)) := by
  rw [G19_12_formula]
  exact vasyuninBEntry_12_19_eval

def interval_19_12 : NamedVasyuninInterval :=
{
  h := 19
  k := 12
  lower := (2970771/42290000)
  upper := (2979229/42290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_12_interval
}

theorem G19_13_formula : baezDuarteGramEntry 19 13 = vasyuninBEntry 13 19 := by
  rw [baezDuarteGramEntry_symm 19 13]
  exact G13_19_formula

theorem G19_13_interval :
    ((((18522891/271090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 13) ∧
    (baezDuarteGramEntry 19 13 ≤ (((18577109/271090000) : ℚ) : ℝ)) := by
  rw [G19_13_formula]
  exact vasyuninBEntry_13_19_eval

def interval_19_13 : NamedVasyuninInterval :=
{
  h := 19
  k := 13
  lower := (18522891/271090000)
  upper := (18577109/271090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_13_interval
}

theorem G19_14_formula : baezDuarteGramEntry 19 14 = vasyuninBEntry 14 19 := by
  rw [baezDuarteGramEntry_symm 19 14]
  exact G14_19_formula

theorem G19_14_interval :
    ((((19860119/298810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 14) ∧
    (baezDuarteGramEntry 19 14 ≤ (((19919881/298810000) : ℚ) : ℝ)) := by
  rw [G19_14_formula]
  exact vasyuninBEntry_14_19_eval

def interval_19_14 : NamedVasyuninInterval :=
{
  h := 19
  k := 14
  lower := (19860119/298810000)
  upper := (19919881/298810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_14_interval
}

theorem G19_15_formula : baezDuarteGramEntry 19 15 = vasyuninBEntry 15 19 := by
  rw [baezDuarteGramEntry_symm 19 15]
  exact G15_19_formula

theorem G19_15_interval :
    ((((3683343/56570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 15) ∧
    (baezDuarteGramEntry 19 15 ≤ (((3694657/56570000) : ℚ) : ℝ)) := by
  rw [G19_15_formula]
  exact vasyuninBEntry_15_19_eval

def interval_19_15 : NamedVasyuninInterval :=
{
  h := 19
  k := 15
  lower := (3683343/56570000)
  upper := (3694657/56570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_15_interval
}

theorem G19_16_formula : baezDuarteGramEntry 19 16 = vasyuninBEntry 16 19 := by
  rw [baezDuarteGramEntry_symm 19 16]
  exact G16_19_formula

theorem G19_16_interval :
    ((((33687533/524670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 16) ∧
    (baezDuarteGramEntry 19 16 ≤ (((33792467/524670000) : ℚ) : ℝ)) := by
  rw [G19_16_formula]
  exact vasyuninBEntry_16_19_eval

def interval_19_16 : NamedVasyuninInterval :=
{
  h := 19
  k := 16
  lower := (33687533/524670000)
  upper := (33792467/524670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_16_interval
}

theorem G19_17_formula : baezDuarteGramEntry 19 17 = vasyuninBEntry 17 19 := by
  rw [baezDuarteGramEntry_symm 19 17]
  exact G17_19_formula

theorem G19_17_interval :
    ((((9257493/145070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 17) ∧
    (baezDuarteGramEntry 19 17 ≤ (((9286507/145070000) : ℚ) : ℝ)) := by
  rw [G19_17_formula]
  exact vasyuninBEntry_17_19_eval

def interval_19_17 : NamedVasyuninInterval :=
{
  h := 19
  k := 17
  lower := (9257493/145070000)
  upper := (9286507/145070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_17_interval
}

theorem G19_18_formula : baezDuarteGramEntry 19 18 = vasyuninBEntry 18 19 := by
  rw [baezDuarteGramEntry_symm 19 18]
  exact G18_19_formula

theorem G19_18_interval :
    ((((30397601/473990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 18) ∧
    (baezDuarteGramEntry 19 18 ≤ (((30492399/473990000) : ℚ) : ℝ)) := by
  rw [G19_18_formula]
  exact vasyuninBEntry_18_19_eval

def interval_19_18 : NamedVasyuninInterval :=
{
  h := 19
  k := 18
  lower := (30397601/473990000)
  upper := (30492399/473990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_18_interval
}

theorem G19_19_formula_eq : baezDuarteGramEntry 19 19 = (1 / (19 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 19 := by norm_num
  rw [baez_duarte_diagonal_scaling 19 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G19_19_log_gamma_interval :
  ((((14183591/214090000) : ℚ) : ℝ) ≤ (1 / (19 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (19 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((14226409/214090000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 19 (by norm_num)
  constructor
  · have : ((((14183591/214090000) : ℚ) : ℝ) ≤ (1 / (19 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (19 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((14226409/214090000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G19_19_interval : ((((14183591/214090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 19) ∧ (baezDuarteGramEntry 19 19 ≤ (((14226409/214090000) : ℚ) : ℝ)) := by
  rw [G19_19_formula_eq]
  exact G19_19_log_gamma_interval

def interval_19_19 : NamedVasyuninInterval :=
{
  h := 19
  k := 19
  lower := (14183591/214090000)
  upper := (14226409/214090000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G19_19_interval
}

theorem G19_20_formula : baezDuarteGramEntry 19 20 = vasyuninBEntry 19 20 := vasyuninBEntry_correct_axiom 19 20 (by norm_num) (by norm_num)

theorem vasyuninBEntry_19_20_eval :
    ((((54370809/891910000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 20) ∧
    (vasyuninBEntry 19 20 ≤ (((54549191/891910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1920_formula_bound
  constructor <;> linarith

theorem G19_20_interval :
    ((((54370809/891910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 20) ∧
    (baezDuarteGramEntry 19 20 ≤ (((54549191/891910000) : ℚ) : ℝ)) := by
  rw [G19_20_formula]
  exact vasyuninBEntry_19_20_eval

def interval_19_20 : NamedVasyuninInterval :=
{
  h := 19
  k := 20
  lower := (54370809/891910000)
  upper := (54549191/891910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_20_interval
}

theorem G20_1_formula : baezDuarteGramEntry 20 1 = vasyuninBEntry 1 20 := by
  rw [baezDuarteGramEntry_symm 20 1]
  exact G1_20_formula

theorem G20_1_interval :
    ((((44721031/339690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 1) ∧
    (baezDuarteGramEntry 20 1 ≤ (((44788969/339690000) : ℚ) : ℝ)) := by
  rw [G20_1_formula]
  exact vasyuninBEntry_1_20_eval

def interval_20_1 : NamedVasyuninInterval :=
{
  h := 20
  k := 1
  lower := (44721031/339690000)
  upper := (44788969/339690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_1_interval
}

theorem G20_2_formula : baezDuarteGramEntry 20 2 = vasyuninBEntry 2 20 := by
  rw [baezDuarteGramEntry_symm 20 2]
  exact G2_20_formula

theorem G20_2_interval :
    ((((40714493/355070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 2) ∧
    (baezDuarteGramEntry 20 2 ≤ (((40785507/355070000) : ℚ) : ℝ)) := by
  rw [G20_2_formula]
  exact vasyuninBEntry_2_20_eval

def interval_20_2 : NamedVasyuninInterval :=
{
  h := 20
  k := 2
  lower := (40714493/355070000)
  upper := (40785507/355070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_2_interval
}

theorem G20_3_formula : baezDuarteGramEntry 20 3 = vasyuninBEntry 3 20 := by
  rw [baezDuarteGramEntry_symm 20 3]
  exact G3_20_formula

theorem G20_3_interval :
    ((((37633689/363110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 3) ∧
    (baezDuarteGramEntry 20 3 ≤ (((37706311/363110000) : ℚ) : ℝ)) := by
  rw [G20_3_formula]
  exact vasyuninBEntry_3_20_eval

def interval_20_3 : NamedVasyuninInterval :=
{
  h := 20
  k := 3
  lower := (37633689/363110000)
  upper := (37706311/363110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_3_interval
}

theorem G20_4_formula : baezDuarteGramEntry 20 4 = vasyuninBEntry 4 20 := by
  rw [baezDuarteGramEntry_symm 20 4]
  exact G4_20_formula

theorem G20_4_interval :
    ((((32112239/327610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 4) ∧
    (baezDuarteGramEntry 20 4 ≤ (((32177761/327610000) : ℚ) : ℝ)) := by
  rw [G20_4_formula]
  exact vasyuninBEntry_4_20_eval

def interval_20_4 : NamedVasyuninInterval :=
{
  h := 20
  k := 4
  lower := (32112239/327610000)
  upper := (32177761/327610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_4_interval
}

theorem G20_5_formula : baezDuarteGramEntry 20 5 = vasyuninBEntry 5 20 := by
  rw [baezDuarteGramEntry_symm 20 5]
  exact G5_20_formula

theorem G20_5_interval :
    ((((21841459/235410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 5) ∧
    (baezDuarteGramEntry 20 5 ≤ (((21888541/235410000) : ℚ) : ℝ)) := by
  rw [G20_5_formula]
  exact vasyuninBEntry_5_20_eval

def interval_20_5 : NamedVasyuninInterval :=
{
  h := 20
  k := 5
  lower := (21841459/235410000)
  upper := (21888541/235410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_5_interval
}

theorem G20_6_formula : baezDuarteGramEntry 20 6 = vasyuninBEntry 6 20 := by
  rw [baezDuarteGramEntry_symm 20 6]
  exact G6_20_formula

theorem G20_6_interval :
    ((((32207631/373690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 6) ∧
    (baezDuarteGramEntry 20 6 ≤ (((32282369/373690000) : ℚ) : ℝ)) := by
  rw [G20_6_formula]
  exact vasyuninBEntry_6_20_eval

def interval_20_6 : NamedVasyuninInterval :=
{
  h := 20
  k := 6
  lower := (32207631/373690000)
  upper := (32282369/373690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_6_interval
}

theorem G20_7_formula : baezDuarteGramEntry 20 7 = vasyuninBEntry 7 20 := by
  rw [baezDuarteGramEntry_symm 20 7]
  exact G7_20_formula

theorem G20_7_interval :
    ((((78045703/942970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 7) ∧
    (baezDuarteGramEntry 20 7 ≤ (((78234297/942970000) : ℚ) : ℝ)) := by
  rw [G20_7_formula]
  exact vasyuninBEntry_7_20_eval

def interval_20_7 : NamedVasyuninInterval :=
{
  h := 20
  k := 7
  lower := (78045703/942970000)
  upper := (78234297/942970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_7_interval
}

theorem G20_8_formula : baezDuarteGramEntry 20 8 = vasyuninBEntry 8 20 := by
  rw [baezDuarteGramEntry_symm 20 8]
  exact G8_20_formula

theorem G20_8_interval :
    ((((9115961/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 8) ∧
    (baezDuarteGramEntry 20 8 ≤ (((9139039/115390000) : ℚ) : ℝ)) := by
  rw [G20_8_formula]
  exact vasyuninBEntry_8_20_eval

def interval_20_8 : NamedVasyuninInterval :=
{
  h := 20
  k := 8
  lower := (9115961/115390000)
  upper := (9139039/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_8_interval
}

theorem G20_9_formula : baezDuarteGramEntry 20 9 = vasyuninBEntry 9 20 := by
  rw [baezDuarteGramEntry_symm 20 9]
  exact G9_20_formula

theorem G20_9_interval :
    ((((6915927/90730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 9) ∧
    (baezDuarteGramEntry 20 9 ≤ (((6934073/90730000) : ℚ) : ℝ)) := by
  rw [G20_9_formula]
  exact vasyuninBEntry_9_20_eval

def interval_20_9 : NamedVasyuninInterval :=
{
  h := 20
  k := 9
  lower := (6915927/90730000)
  upper := (6934073/90730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_9_interval
}

theorem G20_10_formula : baezDuarteGramEntry 20 10 = vasyuninBEntry 10 20 := by
  rw [baezDuarteGramEntry_symm 20 10]
  exact G10_20_formula

theorem G20_10_interval :
    ((((73694443/955570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 10) ∧
    (baezDuarteGramEntry 20 10 ≤ (((73885557/955570000) : ℚ) : ℝ)) := by
  rw [G20_10_formula]
  exact vasyuninBEntry_10_20_eval

def interval_20_10 : NamedVasyuninInterval :=
{
  h := 20
  k := 10
  lower := (73694443/955570000)
  upper := (73885557/955570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_10_interval
}

theorem G20_11_formula : baezDuarteGramEntry 20 11 = vasyuninBEntry 11 20 := by
  rw [baezDuarteGramEntry_symm 20 11]
  exact G11_20_formula

theorem G20_11_interval :
    ((((38505797/542030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 11) ∧
    (baezDuarteGramEntry 20 11 ≤ (((38614203/542030000) : ℚ) : ℝ)) := by
  rw [G20_11_formula]
  exact vasyuninBEntry_11_20_eval

def interval_20_11 : NamedVasyuninInterval :=
{
  h := 20
  k := 11
  lower := (38505797/542030000)
  upper := (38614203/542030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_11_interval
}

theorem G20_12_formula : baezDuarteGramEntry 20 12 = vasyuninBEntry 12 20 := by
  rw [baezDuarteGramEntry_symm 20 12]
  exact G12_20_formula

theorem G20_12_interval :
    ((((20140507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 12) ∧
    (baezDuarteGramEntry 20 12 ≤ (((20199493/294930000) : ℚ) : ℝ)) := by
  rw [G20_12_formula]
  exact vasyuninBEntry_12_20_eval

def interval_20_12 : NamedVasyuninInterval :=
{
  h := 20
  k := 12
  lower := (20140507/294930000)
  upper := (20199493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_12_interval
}

theorem G20_13_formula : baezDuarteGramEntry 20 13 = vasyuninBEntry 13 20 := by
  rw [baezDuarteGramEntry_symm 20 13]
  exact G13_20_formula

theorem G20_13_interval :
    ((((2653489/40110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 13) ∧
    (baezDuarteGramEntry 20 13 ≤ (((2661511/40110000) : ℚ) : ℝ)) := by
  rw [G20_13_formula]
  exact vasyuninBEntry_13_20_eval

def interval_20_13 : NamedVasyuninInterval :=
{
  h := 20
  k := 13
  lower := (2653489/40110000)
  upper := (2661511/40110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_13_interval
}

theorem G20_14_formula : baezDuarteGramEntry 20 14 = vasyuninBEntry 14 20 := by
  rw [baezDuarteGramEntry_symm 20 14]
  exact G14_20_formula

theorem G20_14_interval :
    ((((43302617/673830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 14) ∧
    (baezDuarteGramEntry 20 14 ≤ (((43437383/673830000) : ℚ) : ℝ)) := by
  rw [G20_14_formula]
  exact vasyuninBEntry_14_20_eval

def interval_20_14 : NamedVasyuninInterval :=
{
  h := 20
  k := 14
  lower := (43302617/673830000)
  upper := (43437383/673830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_14_interval
}

theorem G20_15_formula : baezDuarteGramEntry 20 15 = vasyuninBEntry 15 20 := by
  rw [baezDuarteGramEntry_symm 20 15]
  exact G15_20_formula

theorem G20_15_interval :
    ((((2523993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 15) ∧
    (baezDuarteGramEntry 20 15 ≤ (((2532007/40070000) : ℚ) : ℝ)) := by
  rw [G20_15_formula]
  exact vasyuninBEntry_15_20_eval

def interval_20_15 : NamedVasyuninInterval :=
{
  h := 20
  k := 15
  lower := (2523993/40070000)
  upper := (2532007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_15_interval
}

theorem G20_16_formula : baezDuarteGramEntry 20 16 = vasyuninBEntry 16 20 := by
  rw [baezDuarteGramEntry_symm 20 16]
  exact G16_20_formula

theorem G20_16_interval :
    ((((21470227/347730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 16) ∧
    (baezDuarteGramEntry 20 16 ≤ (((21539773/347730000) : ℚ) : ℝ)) := by
  rw [G20_16_formula]
  exact vasyuninBEntry_16_20_eval

def interval_20_16 : NamedVasyuninInterval :=
{
  h := 20
  k := 16
  lower := (21470227/347730000)
  upper := (21539773/347730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_16_interval
}

theorem G20_17_formula : baezDuarteGramEntry 20 17 = vasyuninBEntry 17 20 := by
  rw [baezDuarteGramEntry_symm 20 17]
  exact G17_20_formula

theorem G20_17_interval :
    ((((43069279/707210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 17) ∧
    (baezDuarteGramEntry 20 17 ≤ (((43210721/707210000) : ℚ) : ℝ)) := by
  rw [G20_17_formula]
  exact vasyuninBEntry_17_20_eval

def interval_20_17 : NamedVasyuninInterval :=
{
  h := 20
  k := 17
  lower := (43069279/707210000)
  upper := (43210721/707210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_17_interval
}

theorem G20_18_formula : baezDuarteGramEntry 20 18 = vasyuninBEntry 18 20 := by
  rw [baezDuarteGramEntry_symm 20 18]
  exact G18_20_formula

theorem G20_18_interval :
    ((((44356831/731690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 18) ∧
    (baezDuarteGramEntry 20 18 ≤ (((44503169/731690000) : ℚ) : ℝ)) := by
  rw [G20_18_formula]
  exact vasyuninBEntry_18_20_eval

def interval_20_18 : NamedVasyuninInterval :=
{
  h := 20
  k := 18
  lower := (44356831/731690000)
  upper := (44503169/731690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_18_interval
}

theorem G20_19_formula : baezDuarteGramEntry 20 19 = vasyuninBEntry 19 20 := by
  rw [baezDuarteGramEntry_symm 20 19]
  exact G19_20_formula

theorem G20_19_interval :
    ((((54370809/891910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 19) ∧
    (baezDuarteGramEntry 20 19 ≤ (((54549191/891910000) : ℚ) : ℝ)) := by
  rw [G20_19_formula]
  exact vasyuninBEntry_19_20_eval

def interval_20_19 : NamedVasyuninInterval :=
{
  h := 20
  k := 19
  lower := (54370809/891910000)
  upper := (54549191/891910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_19_interval
}

theorem G20_20_formula_eq : baezDuarteGramEntry 20 20 = (1 / (20 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 20 := by norm_num
  rw [baez_duarte_diagonal_scaling 20 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G20_20_log_gamma_interval :
  ((((19848461/315390000) : ℚ) : ℝ) ≤ (1 / (20 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (20 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((19911539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 20 (by norm_num)
  constructor
  · have : ((((19848461/315390000) : ℚ) : ℝ) ≤ (1 / (20 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (20 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((19911539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G20_20_interval : ((((19848461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 20) ∧ (baezDuarteGramEntry 20 20 ≤ (((19911539/315390000) : ℚ) : ℝ)) := by
  rw [G20_20_formula_eq]
  exact G20_20_log_gamma_interval

def interval_20_20 : NamedVasyuninInterval :=
{
  h := 20
  k := 20
  lower := (19848461/315390000)
  upper := (19911539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G20_20_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN20
