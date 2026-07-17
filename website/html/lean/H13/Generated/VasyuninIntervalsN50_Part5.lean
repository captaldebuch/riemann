import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part1
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part2
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part3
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part4

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

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

theorem G19_20_formula : baezDuarteGramEntry 19 20 = vasyuninBEntry 19 20 := vasyuninBEntry_correct_axiom 19 20

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

theorem G19_21_formula : baezDuarteGramEntry 19 21 = vasyuninBEntry 19 21 := vasyuninBEntry_correct_axiom 19 21

theorem vasyuninBEntry_19_21_eval :
    ((((4814659/83410000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 21) ∧
    (vasyuninBEntry 19 21 ≤ (((4831341/83410000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1921_formula_bound
  constructor <;> linarith

theorem G19_21_interval :
    ((((4814659/83410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 21) ∧
    (baezDuarteGramEntry 19 21 ≤ (((4831341/83410000) : ℚ) : ℝ)) := by
  rw [G19_21_formula]
  exact vasyuninBEntry_19_21_eval

def interval_19_21 : NamedVasyuninInterval :=
{
  h := 19
  k := 21
  lower := (4814659/83410000)
  upper := (4831341/83410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_21_interval
}

theorem G19_22_formula : baezDuarteGramEntry 19 22 = vasyuninBEntry 19 22 := vasyuninBEntry_correct_axiom 19 22

theorem vasyuninBEntry_19_22_eval :
    ((((110893/2007500) : ℚ) : ℝ) ≤ vasyuninBEntry 19 22) ∧
    (vasyuninBEntry 19 22 ≤ (((222589/4015000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1922_formula_bound
  constructor <;> linarith

theorem G19_22_interval :
    ((((110893/2007500) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 22) ∧
    (baezDuarteGramEntry 19 22 ≤ (((222589/4015000) : ℚ) : ℝ)) := by
  rw [G19_22_formula]
  exact vasyuninBEntry_19_22_eval

def interval_19_22 : NamedVasyuninInterval :=
{
  h := 19
  k := 22
  lower := (110893/2007500)
  upper := (222589/4015000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_22_interval
}

theorem G19_23_formula : baezDuarteGramEntry 19 23 = vasyuninBEntry 19 23 := vasyuninBEntry_correct_axiom 19 23

theorem vasyuninBEntry_19_23_eval :
    ((((11945051/224490000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 23) ∧
    (vasyuninBEntry 19 23 ≤ (((11989949/224490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1923_formula_bound
  constructor <;> linarith

theorem G19_23_interval :
    ((((11945051/224490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 23) ∧
    (baezDuarteGramEntry 19 23 ≤ (((11989949/224490000) : ℚ) : ℝ)) := by
  rw [G19_23_formula]
  exact vasyuninBEntry_19_23_eval

def interval_19_23 : NamedVasyuninInterval :=
{
  h := 19
  k := 23
  lower := (11945051/224490000)
  upper := (11989949/224490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_23_interval
}

theorem G19_24_formula : baezDuarteGramEntry 19 24 = vasyuninBEntry 19 24 := vasyuninBEntry_correct_axiom 19 24

theorem vasyuninBEntry_19_24_eval :
    ((((48465881/941190000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 24) ∧
    (vasyuninBEntry 19 24 ≤ (((48654119/941190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1924_formula_bound
  constructor <;> linarith

theorem G19_24_interval :
    ((((48465881/941190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 24) ∧
    (baezDuarteGramEntry 19 24 ≤ (((48654119/941190000) : ℚ) : ℝ)) := by
  rw [G19_24_formula]
  exact vasyuninBEntry_19_24_eval

def interval_19_24 : NamedVasyuninInterval :=
{
  h := 19
  k := 24
  lower := (48465881/941190000)
  upper := (48654119/941190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_24_interval
}

theorem G19_25_formula : baezDuarteGramEntry 19 25 = vasyuninBEntry 19 25 := vasyuninBEntry_correct_axiom 19 25

theorem vasyuninBEntry_19_25_eval :
    ((((23597829/471710000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 25) ∧
    (vasyuninBEntry 19 25 ≤ (((23692171/471710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1925_formula_bound
  constructor <;> linarith

theorem G19_25_interval :
    ((((23597829/471710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 25) ∧
    (baezDuarteGramEntry 19 25 ≤ (((23692171/471710000) : ℚ) : ℝ)) := by
  rw [G19_25_formula]
  exact vasyuninBEntry_19_25_eval

def interval_19_25 : NamedVasyuninInterval :=
{
  h := 19
  k := 25
  lower := (23597829/471710000)
  upper := (23692171/471710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_25_interval
}

theorem G19_26_formula : baezDuarteGramEntry 19 26 = vasyuninBEntry 19 26 := vasyuninBEntry_correct_axiom 19 26

theorem vasyuninBEntry_19_26_eval :
    ((((2966403/60970000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 26) ∧
    (vasyuninBEntry 19 26 ≤ (((2978597/60970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1926_formula_bound
  constructor <;> linarith

theorem G19_26_interval :
    ((((2966403/60970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 26) ∧
    (baezDuarteGramEntry 19 26 ≤ (((2978597/60970000) : ℚ) : ℝ)) := by
  rw [G19_26_formula]
  exact vasyuninBEntry_19_26_eval

def interval_19_26 : NamedVasyuninInterval :=
{
  h := 19
  k := 26
  lower := (2966403/60970000)
  upper := (2978597/60970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_26_interval
}

theorem G19_27_formula : baezDuarteGramEntry 19 27 = vasyuninBEntry 19 27 := vasyuninBEntry_correct_axiom 19 27

theorem vasyuninBEntry_19_27_eval :
    ((((19972921/420790000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 27) ∧
    (vasyuninBEntry 19 27 ≤ (((20057079/420790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1927_formula_bound
  constructor <;> linarith

theorem G19_27_interval :
    ((((19972921/420790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 27) ∧
    (baezDuarteGramEntry 19 27 ≤ (((20057079/420790000) : ℚ) : ℝ)) := by
  rw [G19_27_formula]
  exact vasyuninBEntry_19_27_eval

def interval_19_27 : NamedVasyuninInterval :=
{
  h := 19
  k := 27
  lower := (19972921/420790000)
  upper := (20057079/420790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_27_interval
}

theorem G19_28_formula : baezDuarteGramEntry 19 28 = vasyuninBEntry 19 28 := vasyuninBEntry_correct_axiom 19 28

theorem vasyuninBEntry_19_28_eval :
    ((((1937337/41630000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 28) ∧
    (vasyuninBEntry 19 28 ≤ (((1945663/41630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1928_formula_bound
  constructor <;> linarith

theorem G19_28_interval :
    ((((1937337/41630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 28) ∧
    (baezDuarteGramEntry 19 28 ≤ (((1945663/41630000) : ℚ) : ℝ)) := by
  rw [G19_28_formula]
  exact vasyuninBEntry_19_28_eval

def interval_19_28 : NamedVasyuninInterval :=
{
  h := 19
  k := 28
  lower := (1937337/41630000)
  upper := (1945663/41630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_28_interval
}

theorem G19_29_formula : baezDuarteGramEntry 19 29 = vasyuninBEntry 19 29 := vasyuninBEntry_correct_axiom 19 29

theorem vasyuninBEntry_19_29_eval :
    ((((7351849/161510000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 29) ∧
    (vasyuninBEntry 19 29 ≤ (((7384151/161510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1929_formula_bound
  constructor <;> linarith

theorem G19_29_interval :
    ((((7351849/161510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 29) ∧
    (baezDuarteGramEntry 19 29 ≤ (((7384151/161510000) : ℚ) : ℝ)) := by
  rw [G19_29_formula]
  exact vasyuninBEntry_19_29_eval

def interval_19_29 : NamedVasyuninInterval :=
{
  h := 19
  k := 29
  lower := (7351849/161510000)
  upper := (7384151/161510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_29_interval
}

theorem G19_30_formula : baezDuarteGramEntry 19 30 = vasyuninBEntry 19 30 := vasyuninBEntry_correct_axiom 19 30

theorem vasyuninBEntry_19_30_eval :
    ((((9328993/210070000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 30) ∧
    (vasyuninBEntry 19 30 ≤ (((9371007/210070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1930_formula_bound
  constructor <;> linarith

theorem G19_30_interval :
    ((((9328993/210070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 30) ∧
    (baezDuarteGramEntry 19 30 ≤ (((9371007/210070000) : ℚ) : ℝ)) := by
  rw [G19_30_formula]
  exact vasyuninBEntry_19_30_eval

def interval_19_30 : NamedVasyuninInterval :=
{
  h := 19
  k := 30
  lower := (9328993/210070000)
  upper := (9371007/210070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_30_interval
}

theorem G19_31_formula : baezDuarteGramEntry 19 31 = vasyuninBEntry 19 31 := vasyuninBEntry_correct_axiom 19 31

theorem vasyuninBEntry_19_31_eval :
    ((((39698773/912270000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 31) ∧
    (vasyuninBEntry 19 31 ≤ (((39881227/912270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1931_formula_bound
  constructor <;> linarith

theorem G19_31_interval :
    ((((39698773/912270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 31) ∧
    (baezDuarteGramEntry 19 31 ≤ (((39881227/912270000) : ℚ) : ℝ)) := by
  rw [G19_31_formula]
  exact vasyuninBEntry_19_31_eval

def interval_19_31 : NamedVasyuninInterval :=
{
  h := 19
  k := 31
  lower := (39698773/912270000)
  upper := (39881227/912270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_31_interval
}

theorem G19_32_formula : baezDuarteGramEntry 19 32 = vasyuninBEntry 19 32 := vasyuninBEntry_correct_axiom 19 32

theorem vasyuninBEntry_19_32_eval :
    ((((327593/7663750) : ℚ) : ℝ) ≤ vasyuninBEntry 19 32) ∧
    (vasyuninBEntry 19 32 ≤ (((1316503/30655000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1932_formula_bound
  constructor <;> linarith

theorem G19_32_interval :
    ((((327593/7663750) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 32) ∧
    (baezDuarteGramEntry 19 32 ≤ (((1316503/30655000) : ℚ) : ℝ)) := by
  rw [G19_32_formula]
  exact vasyuninBEntry_19_32_eval

def interval_19_32 : NamedVasyuninInterval :=
{
  h := 19
  k := 32
  lower := (327593/7663750)
  upper := (1316503/30655000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_32_interval
}

theorem G19_33_formula : baezDuarteGramEntry 19 33 = vasyuninBEntry 19 33 := vasyuninBEntry_correct_axiom 19 33

theorem vasyuninBEntry_19_33_eval :
    ((((7943591/189090000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 33) ∧
    (vasyuninBEntry 19 33 ≤ (((7981409/189090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1933_formula_bound
  constructor <;> linarith

theorem G19_33_interval :
    ((((7943591/189090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 33) ∧
    (baezDuarteGramEntry 19 33 ≤ (((7981409/189090000) : ℚ) : ℝ)) := by
  rw [G19_33_formula]
  exact vasyuninBEntry_19_33_eval

def interval_19_33 : NamedVasyuninInterval :=
{
  h := 19
  k := 33
  lower := (7943591/189090000)
  upper := (7981409/189090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_33_interval
}

theorem G19_34_formula : baezDuarteGramEntry 19 34 = vasyuninBEntry 19 34 := vasyuninBEntry_correct_axiom 19 34

theorem vasyuninBEntry_19_34_eval :
    ((((468867/11330000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 34) ∧
    (vasyuninBEntry 19 34 ≤ (((471133/11330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1934_formula_bound
  constructor <;> linarith

theorem G19_34_interval :
    ((((468867/11330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 34) ∧
    (baezDuarteGramEntry 19 34 ≤ (((471133/11330000) : ℚ) : ℝ)) := by
  rw [G19_34_formula]
  exact vasyuninBEntry_19_34_eval

def interval_19_34 : NamedVasyuninInterval :=
{
  h := 19
  k := 34
  lower := (468867/11330000)
  upper := (471133/11330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_34_interval
}

theorem G19_35_formula : baezDuarteGramEntry 19 35 = vasyuninBEntry 19 35 := vasyuninBEntry_correct_axiom 19 35

theorem vasyuninBEntry_19_35_eval :
    ((((2254483/55170000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 35) ∧
    (vasyuninBEntry 19 35 ≤ (((2265517/55170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1935_formula_bound
  constructor <;> linarith

theorem G19_35_interval :
    ((((2254483/55170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 35) ∧
    (baezDuarteGramEntry 19 35 ≤ (((2265517/55170000) : ℚ) : ℝ)) := by
  rw [G19_35_formula]
  exact vasyuninBEntry_19_35_eval

def interval_19_35 : NamedVasyuninInterval :=
{
  h := 19
  k := 35
  lower := (2254483/55170000)
  upper := (2265517/55170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_35_interval
}

theorem G19_36_formula : baezDuarteGramEntry 19 36 = vasyuninBEntry 19 36 := vasyuninBEntry_correct_axiom 19 36

theorem vasyuninBEntry_19_36_eval :
    ((((6100927/150730000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 36) ∧
    (vasyuninBEntry 19 36 ≤ (((6131073/150730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1936_formula_bound
  constructor <;> linarith

theorem G19_36_interval :
    ((((6100927/150730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 36) ∧
    (baezDuarteGramEntry 19 36 ≤ (((6131073/150730000) : ℚ) : ℝ)) := by
  rw [G19_36_formula]
  exact vasyuninBEntry_19_36_eval

def interval_19_36 : NamedVasyuninInterval :=
{
  h := 19
  k := 36
  lower := (6100927/150730000)
  upper := (6131073/150730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_36_interval
}

theorem G19_37_formula : baezDuarteGramEntry 19 37 = vasyuninBEntry 19 37 := vasyuninBEntry_correct_axiom 19 37

theorem vasyuninBEntry_19_37_eval :
    ((((7229549/179510000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 37) ∧
    (vasyuninBEntry 19 37 ≤ (((7265451/179510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1937_formula_bound
  constructor <;> linarith

theorem G19_37_interval :
    ((((7229549/179510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 37) ∧
    (baezDuarteGramEntry 19 37 ≤ (((7265451/179510000) : ℚ) : ℝ)) := by
  rw [G19_37_formula]
  exact vasyuninBEntry_19_37_eval

def interval_19_37 : NamedVasyuninInterval :=
{
  h := 19
  k := 37
  lower := (7229549/179510000)
  upper := (7265451/179510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_37_interval
}

theorem G19_38_formula : baezDuarteGramEntry 19 38 = vasyuninBEntry 19 38 := vasyuninBEntry_correct_axiom 19 38

theorem vasyuninBEntry_19_38_eval :
    ((((2952717/72830000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 38) ∧
    (vasyuninBEntry 19 38 ≤ (((2967283/72830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 19 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 19)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 19)
  constructor <;> linarith

theorem G19_38_interval :
    ((((2952717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 38) ∧
    (baezDuarteGramEntry 19 38 ≤ (((2967283/72830000) : ℚ) : ℝ)) := by
  rw [G19_38_formula]
  exact vasyuninBEntry_19_38_eval

def interval_19_38 : NamedVasyuninInterval :=
{
  h := 19
  k := 38
  lower := (2952717/72830000)
  upper := (2967283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_38_interval
}

theorem G19_39_formula : baezDuarteGramEntry 19 39 = vasyuninBEntry 19 39 := vasyuninBEntry_correct_axiom 19 39

theorem vasyuninBEntry_19_39_eval :
    ((((6868371/176290000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 39) ∧
    (vasyuninBEntry 19 39 ≤ (((6903629/176290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1939_formula_bound
  constructor <;> linarith

theorem G19_39_interval :
    ((((6868371/176290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 39) ∧
    (baezDuarteGramEntry 19 39 ≤ (((6903629/176290000) : ℚ) : ℝ)) := by
  rw [G19_39_formula]
  exact vasyuninBEntry_19_39_eval

def interval_19_39 : NamedVasyuninInterval :=
{
  h := 19
  k := 39
  lower := (6868371/176290000)
  upper := (6903629/176290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_39_interval
}

theorem G19_40_formula : baezDuarteGramEntry 19 40 = vasyuninBEntry 19 40 := vasyuninBEntry_correct_axiom 19 40

theorem vasyuninBEntry_19_40_eval :
    ((((25602411/675890000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 40) ∧
    (vasyuninBEntry 19 40 ≤ (((25737589/675890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1940_formula_bound
  constructor <;> linarith

theorem G19_40_interval :
    ((((25602411/675890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 40) ∧
    (baezDuarteGramEntry 19 40 ≤ (((25737589/675890000) : ℚ) : ℝ)) := by
  rw [G19_40_formula]
  exact vasyuninBEntry_19_40_eval

def interval_19_40 : NamedVasyuninInterval :=
{
  h := 19
  k := 40
  lower := (25602411/675890000)
  upper := (25737589/675890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_40_interval
}

theorem G19_41_formula : baezDuarteGramEntry 19 41 = vasyuninBEntry 19 41 := vasyuninBEntry_correct_axiom 19 41

theorem vasyuninBEntry_19_41_eval :
    ((((31435011/849890000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 41) ∧
    (vasyuninBEntry 19 41 ≤ (((31604989/849890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1941_formula_bound
  constructor <;> linarith

theorem G19_41_interval :
    ((((31435011/849890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 41) ∧
    (baezDuarteGramEntry 19 41 ≤ (((31604989/849890000) : ℚ) : ℝ)) := by
  rw [G19_41_formula]
  exact vasyuninBEntry_19_41_eval

def interval_19_41 : NamedVasyuninInterval :=
{
  h := 19
  k := 41
  lower := (31435011/849890000)
  upper := (31604989/849890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_41_interval
}

theorem G19_42_formula : baezDuarteGramEntry 19 42 = vasyuninBEntry 19 42 := vasyuninBEntry_correct_axiom 19 42

theorem vasyuninBEntry_19_42_eval :
    ((((24213137/668630000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 42) ∧
    (vasyuninBEntry 19 42 ≤ (((24346863/668630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1942_formula_bound
  constructor <;> linarith

theorem G19_42_interval :
    ((((24213137/668630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 42) ∧
    (baezDuarteGramEntry 19 42 ≤ (((24346863/668630000) : ℚ) : ℝ)) := by
  rw [G19_42_formula]
  exact vasyuninBEntry_19_42_eval

def interval_19_42 : NamedVasyuninInterval :=
{
  h := 19
  k := 42
  lower := (24213137/668630000)
  upper := (24346863/668630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_42_interval
}

theorem G19_43_formula : baezDuarteGramEntry 19 43 = vasyuninBEntry 19 43 := vasyuninBEntry_correct_axiom 19 43

theorem vasyuninBEntry_19_43_eval :
    ((((17121803/481970000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 43) ∧
    (vasyuninBEntry 19 43 ≤ (((17218197/481970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1943_formula_bound
  constructor <;> linarith

theorem G19_43_interval :
    ((((17121803/481970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 43) ∧
    (baezDuarteGramEntry 19 43 ≤ (((17218197/481970000) : ℚ) : ℝ)) := by
  rw [G19_43_formula]
  exact vasyuninBEntry_19_43_eval

def interval_19_43 : NamedVasyuninInterval :=
{
  h := 19
  k := 43
  lower := (17121803/481970000)
  upper := (17218197/481970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_43_interval
}

theorem G19_44_formula : baezDuarteGramEntry 19 44 = vasyuninBEntry 19 44 := vasyuninBEntry_correct_axiom 19 44

theorem vasyuninBEntry_19_44_eval :
    ((((2071067/59330000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 44) ∧
    (vasyuninBEntry 19 44 ≤ (((2082933/59330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1944_formula_bound
  constructor <;> linarith

theorem G19_44_interval :
    ((((2071067/59330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 44) ∧
    (baezDuarteGramEntry 19 44 ≤ (((2082933/59330000) : ℚ) : ℝ)) := by
  rw [G19_44_formula]
  exact vasyuninBEntry_19_44_eval

def interval_19_44 : NamedVasyuninInterval :=
{
  h := 19
  k := 44
  lower := (2071067/59330000)
  upper := (2082933/59330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_44_interval
}

theorem G19_45_formula : baezDuarteGramEntry 19 45 = vasyuninBEntry 19 45 := vasyuninBEntry_correct_axiom 19 45

theorem vasyuninBEntry_19_45_eval :
    ((((1547989/45110000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 45) ∧
    (vasyuninBEntry 19 45 ≤ (((1557011/45110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1945_formula_bound
  constructor <;> linarith

theorem G19_45_interval :
    ((((1547989/45110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 45) ∧
    (baezDuarteGramEntry 19 45 ≤ (((1557011/45110000) : ℚ) : ℝ)) := by
  rw [G19_45_formula]
  exact vasyuninBEntry_19_45_eval

def interval_19_45 : NamedVasyuninInterval :=
{
  h := 19
  k := 45
  lower := (1547989/45110000)
  upper := (1557011/45110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_45_interval
}

theorem G19_46_formula : baezDuarteGramEntry 19 46 = vasyuninBEntry 19 46 := vasyuninBEntry_correct_axiom 19 46

theorem vasyuninBEntry_19_46_eval :
    ((((22294007/659930000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 46) ∧
    (vasyuninBEntry 19 46 ≤ (((22425993/659930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1946_formula_bound
  constructor <;> linarith

theorem G19_46_interval :
    ((((22294007/659930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 46) ∧
    (baezDuarteGramEntry 19 46 ≤ (((22425993/659930000) : ℚ) : ℝ)) := by
  rw [G19_46_formula]
  exact vasyuninBEntry_19_46_eval

def interval_19_46 : NamedVasyuninInterval :=
{
  h := 19
  k := 46
  lower := (22294007/659930000)
  upper := (22425993/659930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_46_interval
}

theorem G19_47_formula : baezDuarteGramEntry 19 47 = vasyuninBEntry 19 47 := vasyuninBEntry_correct_axiom 19 47

theorem vasyuninBEntry_19_47_eval :
    ((((107677/3230000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 47) ∧
    (vasyuninBEntry 19 47 ≤ (((108323/3230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1947_formula_bound
  constructor <;> linarith

theorem G19_47_interval :
    ((((107677/3230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 47) ∧
    (baezDuarteGramEntry 19 47 ≤ (((108323/3230000) : ℚ) : ℝ)) := by
  rw [G19_47_formula]
  exact vasyuninBEntry_19_47_eval

def interval_19_47 : NamedVasyuninInterval :=
{
  h := 19
  k := 47
  lower := (107677/3230000)
  upper := (108323/3230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_47_interval
}

theorem G19_48_formula : baezDuarteGramEntry 19 48 = vasyuninBEntry 19 48 := vasyuninBEntry_correct_axiom 19 48

theorem vasyuninBEntry_19_48_eval :
    ((((29041609/883910000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 48) ∧
    (vasyuninBEntry 19 48 ≤ (((29218391/883910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1948_formula_bound
  constructor <;> linarith

theorem G19_48_interval :
    ((((29041609/883910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 48) ∧
    (baezDuarteGramEntry 19 48 ≤ (((29218391/883910000) : ℚ) : ℝ)) := by
  rw [G19_48_formula]
  exact vasyuninBEntry_19_48_eval

def interval_19_48 : NamedVasyuninInterval :=
{
  h := 19
  k := 48
  lower := (29041609/883910000)
  upper := (29218391/883910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_48_interval
}

theorem G19_49_formula : baezDuarteGramEntry 19 49 = vasyuninBEntry 19 49 := vasyuninBEntry_correct_axiom 19 49

theorem vasyuninBEntry_19_49_eval :
    ((((29658291/917090000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 49) ∧
    (vasyuninBEntry 19 49 ≤ (((29841709/917090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1949_formula_bound
  constructor <;> linarith

theorem G19_49_interval :
    ((((29658291/917090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 49) ∧
    (baezDuarteGramEntry 19 49 ≤ (((29841709/917090000) : ℚ) : ℝ)) := by
  rw [G19_49_formula]
  exact vasyuninBEntry_19_49_eval

def interval_19_49 : NamedVasyuninInterval :=
{
  h := 19
  k := 49
  lower := (29658291/917090000)
  upper := (29841709/917090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_49_interval
}

theorem G19_50_formula : baezDuarteGramEntry 19 50 = vasyuninBEntry 19 50 := vasyuninBEntry_correct_axiom 19 50

theorem vasyuninBEntry_19_50_eval :
    ((((21941223/687770000) : ℚ) : ℝ) ≤ vasyuninBEntry 19 50) ∧
    (vasyuninBEntry 19 50 ≤ (((22078777/687770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_1950_formula_bound
  constructor <;> linarith

theorem G19_50_interval :
    ((((21941223/687770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 19 50) ∧
    (baezDuarteGramEntry 19 50 ≤ (((22078777/687770000) : ℚ) : ℝ)) := by
  rw [G19_50_formula]
  exact vasyuninBEntry_19_50_eval

def interval_19_50 : NamedVasyuninInterval :=
{
  h := 19
  k := 50
  lower := (21941223/687770000)
  upper := (22078777/687770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G19_50_interval
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

theorem G20_21_formula : baezDuarteGramEntry 20 21 = vasyuninBEntry 20 21 := vasyuninBEntry_correct_axiom 20 21

theorem vasyuninBEntry_20_21_eval :
    ((((8423/145000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 21) ∧
    (vasyuninBEntry 20 21 ≤ (((2113/36250) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2021_formula_bound
  constructor <;> linarith

theorem G20_21_interval :
    ((((8423/145000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 21) ∧
    (baezDuarteGramEntry 20 21 ≤ (((2113/36250) : ℚ) : ℝ)) := by
  rw [G20_21_formula]
  exact vasyuninBEntry_20_21_eval

def interval_20_21 : NamedVasyuninInterval :=
{
  h := 20
  k := 21
  lower := (8423/145000)
  upper := (2113/36250)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_21_interval
}

theorem G20_22_formula : baezDuarteGramEntry 20 22 = vasyuninBEntry 20 22 := vasyuninBEntry_correct_axiom 20 22

theorem vasyuninBEntry_20_22_eval :
    ((((39697961/720390000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 22) ∧
    (vasyuninBEntry 20 22 ≤ (((39842039/720390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 11 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G20_22_interval :
    ((((39697961/720390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 22) ∧
    (baezDuarteGramEntry 20 22 ≤ (((39842039/720390000) : ℚ) : ℝ)) := by
  rw [G20_22_formula]
  exact vasyuninBEntry_20_22_eval

def interval_20_22 : NamedVasyuninInterval :=
{
  h := 20
  k := 22
  lower := (39697961/720390000)
  upper := (39842039/720390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_22_interval
}

theorem G20_23_formula : baezDuarteGramEntry 20 23 = vasyuninBEntry 20 23 := vasyuninBEntry_correct_axiom 20 23

theorem vasyuninBEntry_20_23_eval :
    ((((634049/12010000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 23) ∧
    (vasyuninBEntry 20 23 ≤ (((636451/12010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2023_formula_bound
  constructor <;> linarith

theorem G20_23_interval :
    ((((634049/12010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 23) ∧
    (baezDuarteGramEntry 20 23 ≤ (((636451/12010000) : ℚ) : ℝ)) := by
  rw [G20_23_formula]
  exact vasyuninBEntry_20_23_eval

def interval_20_23 : NamedVasyuninInterval :=
{
  h := 20
  k := 23
  lower := (634049/12010000)
  upper := (636451/12010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_23_interval
}

theorem G20_24_formula : baezDuarteGramEntry 20 24 = vasyuninBEntry 20 24 := vasyuninBEntry_correct_axiom 20 24

theorem vasyuninBEntry_20_24_eval :
    ((((8732859/171410000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 24) ∧
    (vasyuninBEntry 20 24 ≤ (((8767141/171410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G20_24_interval :
    ((((8732859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 24) ∧
    (baezDuarteGramEntry 20 24 ≤ (((8767141/171410000) : ℚ) : ℝ)) := by
  rw [G20_24_formula]
  exact vasyuninBEntry_20_24_eval

def interval_20_24 : NamedVasyuninInterval :=
{
  h := 20
  k := 24
  lower := (8732859/171410000)
  upper := (8767141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_24_interval
}

theorem G20_25_formula : baezDuarteGramEntry 20 25 = vasyuninBEntry 20 25 := vasyuninBEntry_correct_axiom 20 25

theorem vasyuninBEntry_20_25_eval :
    ((((23472461/475390000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 25) ∧
    (vasyuninBEntry 20 25 ≤ (((23567539/475390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G20_25_interval :
    ((((23472461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 25) ∧
    (baezDuarteGramEntry 20 25 ≤ (((23567539/475390000) : ℚ) : ℝ)) := by
  rw [G20_25_formula]
  exact vasyuninBEntry_20_25_eval

def interval_20_25 : NamedVasyuninInterval :=
{
  h := 20
  k := 25
  lower := (23472461/475390000)
  upper := (23567539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_25_interval
}

theorem G20_26_formula : baezDuarteGramEntry 20 26 = vasyuninBEntry 20 26 := vasyuninBEntry_correct_axiom 20 26

theorem vasyuninBEntry_20_26_eval :
    ((((8749733/182670000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 26) ∧
    (vasyuninBEntry 20 26 ≤ (((8786267/182670000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 13 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G20_26_interval :
    ((((8749733/182670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 26) ∧
    (baezDuarteGramEntry 20 26 ≤ (((8786267/182670000) : ℚ) : ℝ)) := by
  rw [G20_26_formula]
  exact vasyuninBEntry_20_26_eval

def interval_20_26 : NamedVasyuninInterval :=
{
  h := 20
  k := 26
  lower := (8749733/182670000)
  upper := (8786267/182670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_26_interval
}

theorem G20_27_formula : baezDuarteGramEntry 20 27 = vasyuninBEntry 20 27 := vasyuninBEntry_correct_axiom 20 27

theorem vasyuninBEntry_20_27_eval :
    ((((7711481/165190000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 27) ∧
    (vasyuninBEntry 20 27 ≤ (((7744519/165190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2027_formula_bound
  constructor <;> linarith

theorem G20_27_interval :
    ((((7711481/165190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 27) ∧
    (baezDuarteGramEntry 20 27 ≤ (((7744519/165190000) : ℚ) : ℝ)) := by
  rw [G20_27_formula]
  exact vasyuninBEntry_20_27_eval

def interval_20_27 : NamedVasyuninInterval :=
{
  h := 20
  k := 27
  lower := (7711481/165190000)
  upper := (7744519/165190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_27_interval
}

theorem G20_28_formula : baezDuarteGramEntry 20 28 = vasyuninBEntry 20 28 := vasyuninBEntry_correct_axiom 20 28

theorem vasyuninBEntry_20_28_eval :
    ((((9070087/199130000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 28) ∧
    (vasyuninBEntry 20 28 ≤ (((9109913/199130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 7 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G20_28_interval :
    ((((9070087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 28) ∧
    (baezDuarteGramEntry 20 28 ≤ (((9109913/199130000) : ℚ) : ℝ)) := by
  rw [G20_28_formula]
  exact vasyuninBEntry_20_28_eval

def interval_20_28 : NamedVasyuninInterval :=
{
  h := 20
  k := 28
  lower := (9070087/199130000)
  upper := (9109913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_28_interval
}

theorem G20_29_formula : baezDuarteGramEntry 20 29 = vasyuninBEntry 20 29 := vasyuninBEntry_correct_axiom 20 29

theorem vasyuninBEntry_20_29_eval :
    ((((5203323/116770000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 29) ∧
    (vasyuninBEntry 20 29 ≤ (((5226677/116770000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2029_formula_bound
  constructor <;> linarith

theorem G20_29_interval :
    ((((5203323/116770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 29) ∧
    (baezDuarteGramEntry 20 29 ≤ (((5226677/116770000) : ℚ) : ℝ)) := by
  rw [G20_29_formula]
  exact vasyuninBEntry_20_29_eval

def interval_20_29 : NamedVasyuninInterval :=
{
  h := 20
  k := 29
  lower := (5203323/116770000)
  upper := (5226677/116770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_29_interval
}

theorem G20_30_formula : baezDuarteGramEntry 20 30 = vasyuninBEntry 20 30 := vasyuninBEntry_correct_axiom 20 30

theorem vasyuninBEntry_20_30_eval :
    ((((38143331/866690000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 30) ∧
    (vasyuninBEntry 20 30 ≤ (((38316669/866690000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 10 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G20_30_interval :
    ((((38143331/866690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 30) ∧
    (baezDuarteGramEntry 20 30 ≤ (((38316669/866690000) : ℚ) : ℝ)) := by
  rw [G20_30_formula]
  exact vasyuninBEntry_20_30_eval

def interval_20_30 : NamedVasyuninInterval :=
{
  h := 20
  k := 30
  lower := (38143331/866690000)
  upper := (38316669/866690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_30_interval
}

theorem G20_31_formula : baezDuarteGramEntry 20 31 = vasyuninBEntry 20 31 := vasyuninBEntry_correct_axiom 20 31

theorem vasyuninBEntry_20_31_eval :
    ((((42580339/996610000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 31) ∧
    (vasyuninBEntry 20 31 ≤ (((42779661/996610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2031_formula_bound
  constructor <;> linarith

theorem G20_31_interval :
    ((((42580339/996610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 31) ∧
    (baezDuarteGramEntry 20 31 ≤ (((42779661/996610000) : ℚ) : ℝ)) := by
  rw [G20_31_formula]
  exact vasyuninBEntry_20_31_eval

def interval_20_31 : NamedVasyuninInterval :=
{
  h := 20
  k := 31
  lower := (42580339/996610000)
  upper := (42779661/996610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_31_interval
}

theorem G20_32_formula : baezDuarteGramEntry 20 32 = vasyuninBEntry 20 32 := vasyuninBEntry_correct_axiom 20 32

theorem vasyuninBEntry_20_32_eval :
    ((((40383511/964890000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 32) ∧
    (vasyuninBEntry 20 32 ≤ (((40576489/964890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 8 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G20_32_interval :
    ((((40383511/964890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 32) ∧
    (baezDuarteGramEntry 20 32 ≤ (((40576489/964890000) : ℚ) : ℝ)) := by
  rw [G20_32_formula]
  exact vasyuninBEntry_20_32_eval

def interval_20_32 : NamedVasyuninInterval :=
{
  h := 20
  k := 32
  lower := (40383511/964890000)
  upper := (40576489/964890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_32_interval
}

theorem G20_33_formula : baezDuarteGramEntry 20 33 = vasyuninBEntry 20 33 := vasyuninBEntry_correct_axiom 20 33

theorem vasyuninBEntry_20_33_eval :
    ((((37528661/913390000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 33) ∧
    (vasyuninBEntry 20 33 ≤ (((37711339/913390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2033_formula_bound
  constructor <;> linarith

theorem G20_33_interval :
    ((((37528661/913390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 33) ∧
    (baezDuarteGramEntry 20 33 ≤ (((37711339/913390000) : ℚ) : ℝ)) := by
  rw [G20_33_formula]
  exact vasyuninBEntry_20_33_eval

def interval_20_33 : NamedVasyuninInterval :=
{
  h := 20
  k := 33
  lower := (37528661/913390000)
  upper := (37711339/913390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_33_interval
}

theorem G20_34_formula : baezDuarteGramEntry 20 34 = vasyuninBEntry 20 34 := vasyuninBEntry_correct_axiom 20 34

theorem vasyuninBEntry_20_34_eval :
    ((((17965501/444990000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 34) ∧
    (vasyuninBEntry 20 34 ≤ (((18054499/444990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 17 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G20_34_interval :
    ((((17965501/444990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 34) ∧
    (baezDuarteGramEntry 20 34 ≤ (((18054499/444990000) : ℚ) : ℝ)) := by
  rw [G20_34_formula]
  exact vasyuninBEntry_20_34_eval

def interval_20_34 : NamedVasyuninInterval :=
{
  h := 20
  k := 34
  lower := (17965501/444990000)
  upper := (18054499/444990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_34_interval
}

theorem G20_35_formula : baezDuarteGramEntry 20 35 = vasyuninBEntry 20 35 := vasyuninBEntry_correct_axiom 20 35

theorem vasyuninBEntry_20_35_eval :
    ((((38742621/973790000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 35) ∧
    (vasyuninBEntry 20 35 ≤ (((38937379/973790000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 7 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G20_35_interval :
    ((((38742621/973790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 35) ∧
    (baezDuarteGramEntry 20 35 ≤ (((38937379/973790000) : ℚ) : ℝ)) := by
  rw [G20_35_formula]
  exact vasyuninBEntry_20_35_eval

def interval_20_35 : NamedVasyuninInterval :=
{
  h := 20
  k := 35
  lower := (38742621/973790000)
  upper := (38937379/973790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_35_interval
}

theorem G20_36_formula : baezDuarteGramEntry 20 36 = vasyuninBEntry 20 36 := vasyuninBEntry_correct_axiom 20 36

theorem vasyuninBEntry_20_36_eval :
    ((((4299039/109610000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 36) ∧
    (vasyuninBEntry 20 36 ≤ (((4320961/109610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 9 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G20_36_interval :
    ((((4299039/109610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 36) ∧
    (baezDuarteGramEntry 20 36 ≤ (((4320961/109610000) : ℚ) : ℝ)) := by
  rw [G20_36_formula]
  exact vasyuninBEntry_20_36_eval

def interval_20_36 : NamedVasyuninInterval :=
{
  h := 20
  k := 36
  lower := (4299039/109610000)
  upper := (4320961/109610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_36_interval
}

theorem G20_37_formula : baezDuarteGramEntry 20 37 = vasyuninBEntry 20 37 := vasyuninBEntry_correct_axiom 20 37

theorem vasyuninBEntry_20_37_eval :
    ((((7464737/192630000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 37) ∧
    (vasyuninBEntry 20 37 ≤ (((7503263/192630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2037_formula_bound
  constructor <;> linarith

theorem G20_37_interval :
    ((((7464737/192630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 37) ∧
    (baezDuarteGramEntry 20 37 ≤ (((7503263/192630000) : ℚ) : ℝ)) := by
  rw [G20_37_formula]
  exact vasyuninBEntry_20_37_eval

def interval_20_37 : NamedVasyuninInterval :=
{
  h := 20
  k := 37
  lower := (7464737/192630000)
  upper := (7503263/192630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_37_interval
}

theorem G20_38_formula : baezDuarteGramEntry 20 38 = vasyuninBEntry 20 38 := vasyuninBEntry_correct_axiom 20 38

theorem vasyuninBEntry_20_38_eval :
    ((((4625461/120390000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 38) ∧
    (vasyuninBEntry 20 38 ≤ (((4649539/120390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G20_38_interval :
    ((((4625461/120390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 38) ∧
    (baezDuarteGramEntry 20 38 ≤ (((4649539/120390000) : ℚ) : ℝ)) := by
  rw [G20_38_formula]
  exact vasyuninBEntry_20_38_eval

def interval_20_38 : NamedVasyuninInterval :=
{
  h := 20
  k := 38
  lower := (4625461/120390000)
  upper := (4649539/120390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_38_interval
}

theorem G20_39_formula : baezDuarteGramEntry 20 39 = vasyuninBEntry 20 39 := vasyuninBEntry_correct_axiom 20 39

theorem vasyuninBEntry_20_39_eval :
    ((((36454699/953010000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 39) ∧
    (vasyuninBEntry 20 39 ≤ (((36645301/953010000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2039_formula_bound
  constructor <;> linarith

theorem G20_39_interval :
    ((((36454699/953010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 39) ∧
    (baezDuarteGramEntry 20 39 ≤ (((36645301/953010000) : ℚ) : ℝ)) := by
  rw [G20_39_formula]
  exact vasyuninBEntry_20_39_eval

def interval_20_39 : NamedVasyuninInterval :=
{
  h := 20
  k := 39
  lower := (36454699/953010000)
  upper := (36645301/953010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_39_interval
}

theorem G20_40_formula : baezDuarteGramEntry 20 40 = vasyuninBEntry 20 40 := vasyuninBEntry_correct_axiom 20 40

theorem vasyuninBEntry_20_40_eval :
    ((((2804717/72830000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 40) ∧
    (vasyuninBEntry 20 40 ≤ (((2819283/72830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 20 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 20)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 20)
  constructor <;> linarith

theorem G20_40_interval :
    ((((2804717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 40) ∧
    (baezDuarteGramEntry 20 40 ≤ (((2819283/72830000) : ℚ) : ℝ)) := by
  rw [G20_40_formula]
  exact vasyuninBEntry_20_40_eval

def interval_20_40 : NamedVasyuninInterval :=
{
  h := 20
  k := 40
  lower := (2804717/72830000)
  upper := (2819283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_40_interval
}

theorem G20_41_formula : baezDuarteGramEntry 20 41 = vasyuninBEntry 20 41 := vasyuninBEntry_correct_axiom 20 41

theorem vasyuninBEntry_20_41_eval :
    ((((10003013/269870000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 41) ∧
    (vasyuninBEntry 20 41 ≤ (((10056987/269870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2041_formula_bound
  constructor <;> linarith

theorem G20_41_interval :
    ((((10003013/269870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 41) ∧
    (baezDuarteGramEntry 20 41 ≤ (((10056987/269870000) : ℚ) : ℝ)) := by
  rw [G20_41_formula]
  exact vasyuninBEntry_20_41_eval

def interval_20_41 : NamedVasyuninInterval :=
{
  h := 20
  k := 41
  lower := (10003013/269870000)
  upper := (10056987/269870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_41_interval
}

theorem G20_42_formula : baezDuarteGramEntry 20 42 = vasyuninBEntry 20 42 := vasyuninBEntry_correct_axiom 20 42

theorem vasyuninBEntry_20_42_eval :
    ((((3482347/96530000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 42) ∧
    (vasyuninBEntry 20 42 ≤ (((3501653/96530000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 21 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G20_42_interval :
    ((((3482347/96530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 42) ∧
    (baezDuarteGramEntry 20 42 ≤ (((3501653/96530000) : ℚ) : ℝ)) := by
  rw [G20_42_formula]
  exact vasyuninBEntry_20_42_eval

def interval_20_42 : NamedVasyuninInterval :=
{
  h := 20
  k := 42
  lower := (3482347/96530000)
  upper := (3501653/96530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_42_interval
}

theorem G20_43_formula : baezDuarteGramEntry 20 43 = vasyuninBEntry 20 43 := vasyuninBEntry_correct_axiom 20 43

theorem vasyuninBEntry_20_43_eval :
    ((((867539/24610000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 43) ∧
    (vasyuninBEntry 20 43 ≤ (((872461/24610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2043_formula_bound
  constructor <;> linarith

theorem G20_43_interval :
    ((((867539/24610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 43) ∧
    (baezDuarteGramEntry 20 43 ≤ (((872461/24610000) : ℚ) : ℝ)) := by
  rw [G20_43_formula]
  exact vasyuninBEntry_20_43_eval

def interval_20_43 : NamedVasyuninInterval :=
{
  h := 20
  k := 43
  lower := (867539/24610000)
  upper := (872461/24610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_43_interval
}

theorem G20_44_formula : baezDuarteGramEntry 20 44 = vasyuninBEntry 20 44 := vasyuninBEntry_correct_axiom 20 44

theorem vasyuninBEntry_20_44_eval :
    ((((26573089/769110000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 44) ∧
    (vasyuninBEntry 20 44 ≤ (((26726911/769110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 11 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G20_44_interval :
    ((((26573089/769110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 44) ∧
    (baezDuarteGramEntry 20 44 ≤ (((26726911/769110000) : ℚ) : ℝ)) := by
  rw [G20_44_formula]
  exact vasyuninBEntry_20_44_eval

def interval_20_44 : NamedVasyuninInterval :=
{
  h := 20
  k := 44
  lower := (26573089/769110000)
  upper := (26726911/769110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_44_interval
}

theorem G20_45_formula : baezDuarteGramEntry 20 45 = vasyuninBEntry 20 45 := vasyuninBEntry_correct_axiom 20 45

theorem vasyuninBEntry_20_45_eval :
    ((((537017/15830000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 45) ∧
    (vasyuninBEntry 20 45 ≤ (((540183/15830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 9 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G20_45_interval :
    ((((537017/15830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 45) ∧
    (baezDuarteGramEntry 20 45 ≤ (((540183/15830000) : ℚ) : ℝ)) := by
  rw [G20_45_formula]
  exact vasyuninBEntry_20_45_eval

def interval_20_45 : NamedVasyuninInterval :=
{
  h := 20
  k := 45
  lower := (537017/15830000)
  upper := (540183/15830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_45_interval
}

theorem G20_46_formula : baezDuarteGramEntry 20 46 = vasyuninBEntry 20 46 := vasyuninBEntry_correct_axiom 20 46

theorem vasyuninBEntry_20_46_eval :
    ((((19112641/573590000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 46) ∧
    (vasyuninBEntry 20 46 ≤ (((19227359/573590000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G20_46_interval :
    ((((19112641/573590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 46) ∧
    (baezDuarteGramEntry 20 46 ≤ (((19227359/573590000) : ℚ) : ℝ)) := by
  rw [G20_46_formula]
  exact vasyuninBEntry_20_46_eval

def interval_20_46 : NamedVasyuninInterval :=
{
  h := 20
  k := 46
  lower := (19112641/573590000)
  upper := (19227359/573590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_46_interval
}

theorem G20_47_formula : baezDuarteGramEntry 20 47 = vasyuninBEntry 20 47 := vasyuninBEntry_correct_axiom 20 47

theorem vasyuninBEntry_20_47_eval :
    ((((12686317/386830000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 47) ∧
    (vasyuninBEntry 20 47 ≤ (((12763683/386830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2047_formula_bound
  constructor <;> linarith

theorem G20_47_interval :
    ((((12686317/386830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 47) ∧
    (baezDuarteGramEntry 20 47 ≤ (((12763683/386830000) : ℚ) : ℝ)) := by
  rw [G20_47_formula]
  exact vasyuninBEntry_20_47_eval

def interval_20_47 : NamedVasyuninInterval :=
{
  h := 20
  k := 47
  lower := (12686317/386830000)
  upper := (12763683/386830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_47_interval
}

theorem G20_48_formula : baezDuarteGramEntry 20 48 = vasyuninBEntry 20 48 := vasyuninBEntry_correct_axiom 20 48

theorem vasyuninBEntry_20_48_eval :
    ((((29717979/920210000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 48) ∧
    (vasyuninBEntry 20 48 ≤ (((29902021/920210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 12 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G20_48_interval :
    ((((29717979/920210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 48) ∧
    (baezDuarteGramEntry 20 48 ≤ (((29902021/920210000) : ℚ) : ℝ)) := by
  rw [G20_48_formula]
  exact vasyuninBEntry_20_48_eval

def interval_20_48 : NamedVasyuninInterval :=
{
  h := 20
  k := 48
  lower := (29717979/920210000)
  upper := (29902021/920210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_48_interval
}

theorem G20_49_formula : baezDuarteGramEntry 20 49 = vasyuninBEntry 20 49 := vasyuninBEntry_correct_axiom 20 49

theorem vasyuninBEntry_20_49_eval :
    ((((1109017/34830000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 49) ∧
    (vasyuninBEntry 20 49 ≤ (((1115983/34830000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2049_formula_bound
  constructor <;> linarith

theorem G20_49_interval :
    ((((1109017/34830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 49) ∧
    (baezDuarteGramEntry 20 49 ≤ (((1115983/34830000) : ℚ) : ℝ)) := by
  rw [G20_49_formula]
  exact vasyuninBEntry_20_49_eval

def interval_20_49 : NamedVasyuninInterval :=
{
  h := 20
  k := 49
  lower := (1109017/34830000)
  upper := (1115983/34830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_49_interval
}

theorem G20_50_formula : baezDuarteGramEntry 20 50 = vasyuninBEntry 20 50 := vasyuninBEntry_correct_axiom 20 50

theorem vasyuninBEntry_20_50_eval :
    ((((6092683/193170000) : ℚ) : ℝ) ≤ vasyuninBEntry 20 50) ∧
    (vasyuninBEntry 20 50 ≤ (((6131317/193170000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 5 10 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G20_50_interval :
    ((((6092683/193170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 20 50) ∧
    (baezDuarteGramEntry 20 50 ≤ (((6131317/193170000) : ℚ) : ℝ)) := by
  rw [G20_50_formula]
  exact vasyuninBEntry_20_50_eval

def interval_20_50 : NamedVasyuninInterval :=
{
  h := 20
  k := 50
  lower := (6092683/193170000)
  upper := (6131317/193170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G20_50_interval
}

theorem G21_1_formula : baezDuarteGramEntry 21 1 = vasyuninBEntry 1 21 := by
  rw [baezDuarteGramEntry_symm 21 1]
  exact G1_21_formula

theorem G21_1_interval :
    ((((97053293/767070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 1) ∧
    (baezDuarteGramEntry 21 1 ≤ (((97206707/767070000) : ℚ) : ℝ)) := by
  rw [G21_1_formula]
  exact vasyuninBEntry_1_21_eval

def interval_21_1 : NamedVasyuninInterval :=
{
  h := 21
  k := 1
  lower := (97053293/767070000)
  upper := (97206707/767070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_1_interval
}

theorem G21_2_formula : baezDuarteGramEntry 21 2 = vasyuninBEntry 2 21 := by
  rw [baezDuarteGramEntry_symm 21 2]
  exact G2_21_formula

theorem G21_2_interval :
    ((((36416783/332170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 2) ∧
    (baezDuarteGramEntry 21 2 ≤ (((36483217/332170000) : ℚ) : ℝ)) := by
  rw [G21_2_formula]
  exact vasyuninBEntry_2_21_eval

def interval_21_2 : NamedVasyuninInterval :=
{
  h := 21
  k := 2
  lower := (36416783/332170000)
  upper := (36483217/332170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_2_interval
}

theorem G21_3_formula : baezDuarteGramEntry 21 3 = vasyuninBEntry 3 21 := by
  rw [baezDuarteGramEntry_symm 21 3]
  exact G3_21_formula

theorem G21_3_interval :
    ((((95535399/946010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 3) ∧
    (baezDuarteGramEntry 21 3 ≤ (((95724601/946010000) : ℚ) : ℝ)) := by
  rw [G21_3_formula]
  exact vasyuninBEntry_3_21_eval

def interval_21_3 : NamedVasyuninInterval :=
{
  h := 21
  k := 3
  lower := (95535399/946010000)
  upper := (95724601/946010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_3_interval
}

theorem G21_4_formula : baezDuarteGramEntry 21 4 = vasyuninBEntry 4 21 := by
  rw [baezDuarteGramEntry_symm 21 4]
  exact G4_21_formula

theorem G21_4_interval :
    ((((21699187/233130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 4) ∧
    (baezDuarteGramEntry 21 4 ≤ (((21745813/233130000) : ℚ) : ℝ)) := by
  rw [G21_4_formula]
  exact vasyuninBEntry_4_21_eval

def interval_21_4 : NamedVasyuninInterval :=
{
  h := 21
  k := 4
  lower := (21699187/233130000)
  upper := (21745813/233130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_4_interval
}

theorem G21_5_formula : baezDuarteGramEntry 21 5 = vasyuninBEntry 5 21 := by
  rw [baezDuarteGramEntry_symm 21 5]
  exact G5_21_formula

theorem G21_5_interval :
    ((((95329/1085000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 5) ∧
    (baezDuarteGramEntry 21 5 ≤ (((47773/542500) : ℚ) : ℝ)) := by
  rw [G21_5_formula]
  exact vasyuninBEntry_5_21_eval

def interval_21_5 : NamedVasyuninInterval :=
{
  h := 21
  k := 5
  lower := (95329/1085000)
  upper := (47773/542500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_5_interval
}

theorem G21_6_formula : baezDuarteGramEntry 21 6 = vasyuninBEntry 6 21 := by
  rw [baezDuarteGramEntry_symm 21 6]
  exact G6_21_formula

theorem G21_6_interval :
    ((((76268471/915290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 6) ∧
    (baezDuarteGramEntry 21 6 ≤ (((76451529/915290000) : ℚ) : ℝ)) := by
  rw [G21_6_formula]
  exact vasyuninBEntry_6_21_eval

def interval_21_6 : NamedVasyuninInterval :=
{
  h := 21
  k := 6
  lower := (76268471/915290000)
  upper := (76451529/915290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_6_interval
}

theorem G21_7_formula : baezDuarteGramEntry 21 7 = vasyuninBEntry 7 21 := by
  rw [baezDuarteGramEntry_symm 21 7]
  exact G7_21_formula

theorem G21_7_interval :
    ((((76816371/936290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 7) ∧
    (baezDuarteGramEntry 21 7 ≤ (((77003629/936290000) : ℚ) : ℝ)) := by
  rw [G21_7_formula]
  exact vasyuninBEntry_7_21_eval

def interval_21_7 : NamedVasyuninInterval :=
{
  h := 21
  k := 7
  lower := (76816371/936290000)
  upper := (77003629/936290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_7_interval
}

theorem G21_8_formula : baezDuarteGramEntry 21 8 = vasyuninBEntry 8 21 := by
  rw [baezDuarteGramEntry_symm 21 8]
  exact G8_21_formula

theorem G21_8_interval :
    ((((32896733/432670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 8) ∧
    (baezDuarteGramEntry 21 8 ≤ (((32983267/432670000) : ℚ) : ℝ)) := by
  rw [G21_8_formula]
  exact vasyuninBEntry_8_21_eval

def interval_21_8 : NamedVasyuninInterval :=
{
  h := 21
  k := 8
  lower := (32896733/432670000)
  upper := (32983267/432670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_8_interval
}

theorem G21_9_formula : baezDuarteGramEntry 21 9 = vasyuninBEntry 9 21 := by
  rw [baezDuarteGramEntry_symm 21 9]
  exact G9_21_formula

theorem G21_9_interval :
    ((((65980213/897870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 9) ∧
    (baezDuarteGramEntry 21 9 ≤ (((66159787/897870000) : ℚ) : ℝ)) := by
  rw [G21_9_formula]
  exact vasyuninBEntry_9_21_eval

def interval_21_9 : NamedVasyuninInterval :=
{
  h := 21
  k := 9
  lower := (65980213/897870000)
  upper := (66159787/897870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_9_interval
}

theorem G21_10_formula : baezDuarteGramEntry 21 10 = vasyuninBEntry 10 21 := by
  rw [baezDuarteGramEntry_symm 21 10]
  exact G10_21_formula

theorem G21_10_interval :
    ((((6974347/96530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 10) ∧
    (baezDuarteGramEntry 21 10 ≤ (((6993653/96530000) : ℚ) : ℝ)) := by
  rw [G21_10_formula]
  exact vasyuninBEntry_10_21_eval

def interval_21_10 : NamedVasyuninInterval :=
{
  h := 21
  k := 10
  lower := (6974347/96530000)
  upper := (6993653/96530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_10_interval
}

theorem G21_11_formula : baezDuarteGramEntry 21 11 = vasyuninBEntry 11 21 := by
  rw [baezDuarteGramEntry_symm 21 11]
  exact G11_21_formula

theorem G21_11_interval :
    ((((17212859/246410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 11) ∧
    (baezDuarteGramEntry 21 11 ≤ (((17262141/246410000) : ℚ) : ℝ)) := by
  rw [G21_11_formula]
  exact vasyuninBEntry_11_21_eval

def interval_21_11 : NamedVasyuninInterval :=
{
  h := 21
  k := 11
  lower := (17212859/246410000)
  upper := (17262141/246410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_11_interval
}

theorem G21_12_formula : baezDuarteGramEntry 21 12 = vasyuninBEntry 12 21 := by
  rw [baezDuarteGramEntry_symm 21 12]
  exact G12_21_formula

theorem G21_12_interval :
    ((((49345657/743430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 12) ∧
    (baezDuarteGramEntry 21 12 ≤ (((49494343/743430000) : ℚ) : ℝ)) := by
  rw [G21_12_formula]
  exact vasyuninBEntry_12_21_eval

def interval_21_12 : NamedVasyuninInterval :=
{
  h := 21
  k := 12
  lower := (49345657/743430000)
  upper := (49494343/743430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_12_interval
}

theorem G21_13_formula : baezDuarteGramEntry 21 13 = vasyuninBEntry 13 21 := by
  rw [baezDuarteGramEntry_symm 21 13]
  exact G13_21_formula

theorem G21_13_interval :
    ((((47346051/739490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 13) ∧
    (baezDuarteGramEntry 21 13 ≤ (((47493949/739490000) : ℚ) : ℝ)) := by
  rw [G21_13_formula]
  exact vasyuninBEntry_13_21_eval

def interval_21_13 : NamedVasyuninInterval :=
{
  h := 21
  k := 13
  lower := (47346051/739490000)
  upper := (47493949/739490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_13_interval
}

theorem G21_14_formula : baezDuarteGramEntry 21 14 = vasyuninBEntry 14 21 := by
  rw [baezDuarteGramEntry_symm 21 14]
  exact G14_21_formula

theorem G21_14_interval :
    ((((58586879/931210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 14) ∧
    (baezDuarteGramEntry 21 14 ≤ (((58773121/931210000) : ℚ) : ℝ)) := by
  rw [G21_14_formula]
  exact vasyuninBEntry_14_21_eval

def interval_21_14 : NamedVasyuninInterval :=
{
  h := 21
  k := 14
  lower := (58586879/931210000)
  upper := (58773121/931210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_14_interval
}

theorem G21_15_formula : baezDuarteGramEntry 21 15 = vasyuninBEntry 15 21 := by
  rw [baezDuarteGramEntry_symm 21 15]
  exact G15_21_formula

theorem G21_15_interval :
    ((((12100087/199130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 15) ∧
    (baezDuarteGramEntry 21 15 ≤ (((12139913/199130000) : ℚ) : ℝ)) := by
  rw [G21_15_formula]
  exact vasyuninBEntry_15_21_eval

def interval_21_15 : NamedVasyuninInterval :=
{
  h := 21
  k := 15
  lower := (12100087/199130000)
  upper := (12139913/199130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_15_interval
}

theorem G21_16_formula : baezDuarteGramEntry 21 16 = vasyuninBEntry 16 21 := by
  rw [baezDuarteGramEntry_symm 21 16]
  exact G16_21_formula

theorem G21_16_interval :
    ((((3135981/52690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 16) ∧
    (baezDuarteGramEntry 21 16 ≤ (((3146519/52690000) : ℚ) : ℝ)) := by
  rw [G21_16_formula]
  exact vasyuninBEntry_16_21_eval

def interval_21_16 : NamedVasyuninInterval :=
{
  h := 21
  k := 16
  lower := (3135981/52690000)
  upper := (3146519/52690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_16_interval
}

theorem G21_17_formula : baezDuarteGramEntry 21 17 = vasyuninBEntry 17 21 := by
  rw [baezDuarteGramEntry_symm 21 17]
  exact G17_21_formula

theorem G21_17_interval :
    ((((34800559/594410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 17) ∧
    (baezDuarteGramEntry 21 17 ≤ (((34919441/594410000) : ℚ) : ℝ)) := by
  rw [G21_17_formula]
  exact vasyuninBEntry_17_21_eval

def interval_21_17 : NamedVasyuninInterval :=
{
  h := 21
  k := 17
  lower := (34800559/594410000)
  upper := (34919441/594410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_17_interval
}

theorem G21_18_formula : baezDuarteGramEntry 21 18 = vasyuninBEntry 18 21 := by
  rw [baezDuarteGramEntry_symm 21 18]
  exact G18_21_formula

theorem G21_18_interval :
    ((((50772399/876010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 18) ∧
    (baezDuarteGramEntry 21 18 ≤ (((50947601/876010000) : ℚ) : ℝ)) := by
  rw [G21_18_formula]
  exact vasyuninBEntry_18_21_eval

def interval_21_18 : NamedVasyuninInterval :=
{
  h := 21
  k := 18
  lower := (50772399/876010000)
  upper := (50947601/876010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_18_interval
}

theorem G21_19_formula : baezDuarteGramEntry 21 19 = vasyuninBEntry 19 21 := by
  rw [baezDuarteGramEntry_symm 21 19]
  exact G19_21_formula

theorem G21_19_interval :
    ((((4814659/83410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 19) ∧
    (baezDuarteGramEntry 21 19 ≤ (((4831341/83410000) : ℚ) : ℝ)) := by
  rw [G21_19_formula]
  exact vasyuninBEntry_19_21_eval

def interval_21_19 : NamedVasyuninInterval :=
{
  h := 21
  k := 19
  lower := (4814659/83410000)
  upper := (4831341/83410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_19_interval
}

theorem G21_20_formula : baezDuarteGramEntry 21 20 = vasyuninBEntry 20 21 := by
  rw [baezDuarteGramEntry_symm 21 20]
  exact G20_21_formula

theorem G21_20_interval :
    ((((8423/145000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 20) ∧
    (baezDuarteGramEntry 21 20 ≤ (((2113/36250) : ℚ) : ℝ)) := by
  rw [G21_20_formula]
  exact vasyuninBEntry_20_21_eval

def interval_21_20 : NamedVasyuninInterval :=
{
  h := 21
  k := 20
  lower := (8423/145000)
  upper := (2113/36250)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_20_interval
}

theorem G21_21_formula_eq : baezDuarteGramEntry 21 21 = (1 / (21 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 21 := by norm_num
  rw [baez_duarte_diagonal_scaling 21 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G21_21_log_gamma_interval :
  ((((23595629/393710000) : ℚ) : ℝ) ≤ (1 / (21 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (21 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((23674371/393710000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 21 (by norm_num)
  constructor
  · have : ((((23595629/393710000) : ℚ) : ℝ) ≤ (1 / (21 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (21 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((23674371/393710000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G21_21_interval : ((((23595629/393710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 21) ∧ (baezDuarteGramEntry 21 21 ≤ (((23674371/393710000) : ℚ) : ℝ)) := by
  rw [G21_21_formula_eq]
  exact G21_21_log_gamma_interval

def interval_21_21 : NamedVasyuninInterval :=
{
  h := 21
  k := 21
  lower := (23595629/393710000)
  upper := (23674371/393710000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G21_21_interval
}

theorem G21_22_formula : baezDuarteGramEntry 21 22 = vasyuninBEntry 21 22 := vasyuninBEntry_correct_axiom 21 22

theorem vasyuninBEntry_21_22_eval :
    ((((1708483/30795000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 22) ∧
    (vasyuninBEntry 21 22 ≤ (((857321/15397500) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2122_formula_bound
  constructor <;> linarith

theorem G21_22_interval :
    ((((1708483/30795000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 22) ∧
    (baezDuarteGramEntry 21 22 ≤ (((857321/15397500) : ℚ) : ℝ)) := by
  rw [G21_22_formula]
  exact vasyuninBEntry_21_22_eval

def interval_21_22 : NamedVasyuninInterval :=
{
  h := 21
  k := 22
  lower := (1708483/30795000)
  upper := (857321/15397500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_22_interval
}

theorem G21_23_formula : baezDuarteGramEntry 21 23 = vasyuninBEntry 21 23 := vasyuninBEntry_correct_axiom 21 23

theorem vasyuninBEntry_21_23_eval :
    ((((50703803/961970000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 23) ∧
    (vasyuninBEntry 21 23 ≤ (((50896197/961970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2123_formula_bound
  constructor <;> linarith

theorem G21_23_interval :
    ((((50703803/961970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 23) ∧
    (baezDuarteGramEntry 21 23 ≤ (((50896197/961970000) : ℚ) : ℝ)) := by
  rw [G21_23_formula]
  exact vasyuninBEntry_21_23_eval

def interval_21_23 : NamedVasyuninInterval :=
{
  h := 21
  k := 23
  lower := (50703803/961970000)
  upper := (50896197/961970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_23_interval
}

theorem G21_24_formula : baezDuarteGramEntry 21 24 = vasyuninBEntry 21 24 := vasyuninBEntry_correct_axiom 21 24

theorem vasyuninBEntry_21_24_eval :
    ((((9139929/180710000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 24) ∧
    (vasyuninBEntry 21 24 ≤ (((9176071/180710000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_8_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 8 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_24_interval :
    ((((9139929/180710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 24) ∧
    (baezDuarteGramEntry 21 24 ≤ (((9176071/180710000) : ℚ) : ℝ)) := by
  rw [G21_24_formula]
  exact vasyuninBEntry_21_24_eval

def interval_21_24 : NamedVasyuninInterval :=
{
  h := 21
  k := 24
  lower := (9139929/180710000)
  upper := (9176071/180710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_24_interval
}

theorem G21_25_formula : baezDuarteGramEntry 21 25 = vasyuninBEntry 21 25 := vasyuninBEntry_correct_axiom 21 25

theorem vasyuninBEntry_21_25_eval :
    ((((42063797/862030000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 25) ∧
    (vasyuninBEntry 21 25 ≤ (((42236203/862030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2125_formula_bound
  constructor <;> linarith

theorem G21_25_interval :
    ((((42063797/862030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 25) ∧
    (baezDuarteGramEntry 21 25 ≤ (((42236203/862030000) : ℚ) : ℝ)) := by
  rw [G21_25_formula]
  exact vasyuninBEntry_21_25_eval

def interval_21_25 : NamedVasyuninInterval :=
{
  h := 21
  k := 25
  lower := (42063797/862030000)
  upper := (42236203/862030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_25_interval
}

theorem G21_26_formula : baezDuarteGramEntry 21 26 = vasyuninBEntry 21 26 := vasyuninBEntry_correct_axiom 21 26

theorem vasyuninBEntry_21_26_eval :
    ((((23545219/497810000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 26) ∧
    (vasyuninBEntry 21 26 ≤ (((23644781/497810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2126_formula_bound
  constructor <;> linarith

theorem G21_26_interval :
    ((((23545219/497810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 26) ∧
    (baezDuarteGramEntry 21 26 ≤ (((23644781/497810000) : ℚ) : ℝ)) := by
  rw [G21_26_formula]
  exact vasyuninBEntry_21_26_eval

def interval_21_26 : NamedVasyuninInterval :=
{
  h := 21
  k := 26
  lower := (23545219/497810000)
  upper := (23644781/497810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_26_interval
}

theorem G21_27_formula : baezDuarteGramEntry 21 27 = vasyuninBEntry 21 27 := vasyuninBEntry_correct_axiom 21 27

theorem vasyuninBEntry_21_27_eval :
    ((((11327863/246370000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 27) ∧
    (vasyuninBEntry 21 27 ≤ (((11377137/246370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 9 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_27_interval :
    ((((11327863/246370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 27) ∧
    (baezDuarteGramEntry 21 27 ≤ (((11377137/246370000) : ℚ) : ℝ)) := by
  rw [G21_27_formula]
  exact vasyuninBEntry_21_27_eval

def interval_21_27 : NamedVasyuninInterval :=
{
  h := 21
  k := 27
  lower := (11327863/246370000)
  upper := (11377137/246370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_27_interval
}

theorem G21_28_formula : baezDuarteGramEntry 21 28 = vasyuninBEntry 21 28 := vasyuninBEntry_correct_axiom 21 28

theorem vasyuninBEntry_21_28_eval :
    ((((12611951/280490000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 28) ∧
    (vasyuninBEntry 21 28 ≤ (((12668049/280490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_4_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 4 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G21_28_interval :
    ((((12611951/280490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 28) ∧
    (baezDuarteGramEntry 21 28 ≤ (((12668049/280490000) : ℚ) : ℝ)) := by
  rw [G21_28_formula]
  exact vasyuninBEntry_21_28_eval

def interval_21_28 : NamedVasyuninInterval :=
{
  h := 21
  k := 28
  lower := (12611951/280490000)
  upper := (12668049/280490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_28_interval
}

theorem G21_29_formula : baezDuarteGramEntry 21 29 = vasyuninBEntry 21 29 := vasyuninBEntry_correct_axiom 21 29

theorem vasyuninBEntry_21_29_eval :
    ((((32735151/748490000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 29) ∧
    (vasyuninBEntry 21 29 ≤ (((32884849/748490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2129_formula_bound
  constructor <;> linarith

theorem G21_29_interval :
    ((((32735151/748490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 29) ∧
    (baezDuarteGramEntry 21 29 ≤ (((32884849/748490000) : ℚ) : ℝ)) := by
  rw [G21_29_formula]
  exact vasyuninBEntry_21_29_eval

def interval_21_29 : NamedVasyuninInterval :=
{
  h := 21
  k := 29
  lower := (32735151/748490000)
  upper := (32884849/748490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_29_interval
}

theorem G21_30_formula : baezDuarteGramEntry 21 30 = vasyuninBEntry 21 30 := vasyuninBEntry_correct_axiom 21 30

theorem vasyuninBEntry_21_30_eval :
    ((((531259/12410000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 30) ∧
    (vasyuninBEntry 21 30 ≤ (((533741/12410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_10_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 10 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_30_interval :
    ((((531259/12410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 30) ∧
    (baezDuarteGramEntry 21 30 ≤ (((533741/12410000) : ℚ) : ℝ)) := by
  rw [G21_30_formula]
  exact vasyuninBEntry_21_30_eval

def interval_21_30 : NamedVasyuninInterval :=
{
  h := 21
  k := 30
  lower := (531259/12410000)
  upper := (533741/12410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_30_interval
}

theorem G21_31_formula : baezDuarteGramEntry 21 31 = vasyuninBEntry 21 31 := vasyuninBEntry_correct_axiom 21 31

theorem vasyuninBEntry_21_31_eval :
    ((((2075067/49330000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 31) ∧
    (vasyuninBEntry 21 31 ≤ (((2084933/49330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2131_formula_bound
  constructor <;> linarith

theorem G21_31_interval :
    ((((2075067/49330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 31) ∧
    (baezDuarteGramEntry 21 31 ≤ (((2084933/49330000) : ℚ) : ℝ)) := by
  rw [G21_31_formula]
  exact vasyuninBEntry_21_31_eval

def interval_21_31 : NamedVasyuninInterval :=
{
  h := 21
  k := 31
  lower := (2075067/49330000)
  upper := (2084933/49330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_31_interval
}

theorem G21_32_formula : baezDuarteGramEntry 21 32 = vasyuninBEntry 21 32 := vasyuninBEntry_correct_axiom 21 32

theorem vasyuninBEntry_21_32_eval :
    ((((359129/8710000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 32) ∧
    (vasyuninBEntry 21 32 ≤ (((360871/8710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2132_formula_bound
  constructor <;> linarith

theorem G21_32_interval :
    ((((359129/8710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 32) ∧
    (baezDuarteGramEntry 21 32 ≤ (((360871/8710000) : ℚ) : ℝ)) := by
  rw [G21_32_formula]
  exact vasyuninBEntry_21_32_eval

def interval_21_32 : NamedVasyuninInterval :=
{
  h := 21
  k := 32
  lower := (359129/8710000)
  upper := (360871/8710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_32_interval
}

theorem G21_33_formula : baezDuarteGramEntry 21 33 = vasyuninBEntry 21 33 := vasyuninBEntry_correct_axiom 21 33

theorem vasyuninBEntry_21_33_eval :
    ((((8705901/215990000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 33) ∧
    (vasyuninBEntry 21 33 ≤ (((8749099/215990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 11 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_33_interval :
    ((((8705901/215990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 33) ∧
    (baezDuarteGramEntry 21 33 ≤ (((8749099/215990000) : ℚ) : ℝ)) := by
  rw [G21_33_formula]
  exact vasyuninBEntry_21_33_eval

def interval_21_33 : NamedVasyuninInterval :=
{
  h := 21
  k := 33
  lower := (8705901/215990000)
  upper := (8749099/215990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_33_interval
}

theorem G21_34_formula : baezDuarteGramEntry 21 34 = vasyuninBEntry 21 34 := vasyuninBEntry_correct_axiom 21 34

theorem vasyuninBEntry_21_34_eval :
    ((((30363211/767890000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 34) ∧
    (vasyuninBEntry 21 34 ≤ (((30516789/767890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2134_formula_bound
  constructor <;> linarith

theorem G21_34_interval :
    ((((30363211/767890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 34) ∧
    (baezDuarteGramEntry 21 34 ≤ (((30516789/767890000) : ℚ) : ℝ)) := by
  rw [G21_34_formula]
  exact vasyuninBEntry_21_34_eval

def interval_21_34 : NamedVasyuninInterval :=
{
  h := 21
  k := 34
  lower := (30363211/767890000)
  upper := (30516789/767890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_34_interval
}

theorem G21_35_formula : baezDuarteGramEntry 21 35 = vasyuninBEntry 21 35 := vasyuninBEntry_correct_axiom 21 35

theorem vasyuninBEntry_21_35_eval :
    ((((1792277/45980000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 35) ∧
    (vasyuninBEntry 21 35 ≤ (((1801473/45980000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 5 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G21_35_interval :
    ((((1792277/45980000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 35) ∧
    (baezDuarteGramEntry 21 35 ≤ (((1801473/45980000) : ℚ) : ℝ)) := by
  rw [G21_35_formula]
  exact vasyuninBEntry_21_35_eval

def interval_21_35 : NamedVasyuninInterval :=
{
  h := 21
  k := 35
  lower := (1792277/45980000)
  upper := (1801473/45980000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_35_interval
}

theorem G21_36_formula : baezDuarteGramEntry 21 36 = vasyuninBEntry 21 36 := vasyuninBEntry_correct_axiom 21 36

theorem vasyuninBEntry_21_36_eval :
    ((((20695919/540810000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 36) ∧
    (vasyuninBEntry 21 36 ≤ (((20804081/540810000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 12 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_36_interval :
    ((((20695919/540810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 36) ∧
    (baezDuarteGramEntry 21 36 ≤ (((20804081/540810000) : ℚ) : ℝ)) := by
  rw [G21_36_formula]
  exact vasyuninBEntry_21_36_eval

def interval_21_36 : NamedVasyuninInterval :=
{
  h := 21
  k := 36
  lower := (20695919/540810000)
  upper := (20804081/540810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_36_interval
}

theorem G21_37_formula : baezDuarteGramEntry 21 37 = vasyuninBEntry 21 37 := vasyuninBEntry_correct_axiom 21 37

theorem vasyuninBEntry_21_37_eval :
    ((((3353111/88890000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 37) ∧
    (vasyuninBEntry 21 37 ≤ (((3370889/88890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2137_formula_bound
  constructor <;> linarith

theorem G21_37_interval :
    ((((3353111/88890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 37) ∧
    (baezDuarteGramEntry 21 37 ≤ (((3370889/88890000) : ℚ) : ℝ)) := by
  rw [G21_37_formula]
  exact vasyuninBEntry_21_37_eval

def interval_21_37 : NamedVasyuninInterval :=
{
  h := 21
  k := 37
  lower := (3353111/88890000)
  upper := (3370889/88890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_37_interval
}

theorem G21_38_formula : baezDuarteGramEntry 21 38 = vasyuninBEntry 21 38 := vasyuninBEntry_correct_axiom 21 38

theorem vasyuninBEntry_21_38_eval :
    ((((30627761/822390000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 38) ∧
    (vasyuninBEntry 21 38 ≤ (((30792239/822390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2138_formula_bound
  constructor <;> linarith

theorem G21_38_interval :
    ((((30627761/822390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 38) ∧
    (baezDuarteGramEntry 21 38 ≤ (((30792239/822390000) : ℚ) : ℝ)) := by
  rw [G21_38_formula]
  exact vasyuninBEntry_21_38_eval

def interval_21_38 : NamedVasyuninInterval :=
{
  h := 21
  k := 38
  lower := (30627761/822390000)
  upper := (30792239/822390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_38_interval
}

theorem G21_39_formula : baezDuarteGramEntry 21 39 = vasyuninBEntry 21 39 := vasyuninBEntry_correct_axiom 21 39

theorem vasyuninBEntry_21_39_eval :
    ((((736003/19970000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 39) ∧
    (vasyuninBEntry 21 39 ≤ (((739997/19970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 13 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_39_interval :
    ((((736003/19970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 39) ∧
    (baezDuarteGramEntry 21 39 ≤ (((739997/19970000) : ℚ) : ℝ)) := by
  rw [G21_39_formula]
  exact vasyuninBEntry_21_39_eval

def interval_21_39 : NamedVasyuninInterval :=
{
  h := 21
  k := 39
  lower := (736003/19970000)
  upper := (739997/19970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_39_interval
}

theorem G21_40_formula : baezDuarteGramEntry 21 40 = vasyuninBEntry 21 40 := vasyuninBEntry_correct_axiom 21 40

theorem vasyuninBEntry_21_40_eval :
    ((((441293/12070000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 40) ∧
    (vasyuninBEntry 21 40 ≤ (((443707/12070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2140_formula_bound
  constructor <;> linarith

theorem G21_40_interval :
    ((((441293/12070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 40) ∧
    (baezDuarteGramEntry 21 40 ≤ (((443707/12070000) : ℚ) : ℝ)) := by
  rw [G21_40_formula]
  exact vasyuninBEntry_21_40_eval

def interval_21_40 : NamedVasyuninInterval :=
{
  h := 21
  k := 40
  lower := (441293/12070000)
  upper := (443707/12070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_40_interval
}

theorem G21_41_formula : baezDuarteGramEntry 21 41 = vasyuninBEntry 21 41 := vasyuninBEntry_correct_axiom 21 41

theorem vasyuninBEntry_21_41_eval :
    ((((12096789/332110000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 41) ∧
    (vasyuninBEntry 21 41 ≤ (((12163211/332110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2141_formula_bound
  constructor <;> linarith

theorem G21_41_interval :
    ((((12096789/332110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 41) ∧
    (baezDuarteGramEntry 21 41 ≤ (((12163211/332110000) : ℚ) : ℝ)) := by
  rw [G21_41_formula]
  exact vasyuninBEntry_21_41_eval

def interval_21_41 : NamedVasyuninInterval :=
{
  h := 21
  k := 41
  lower := (12096789/332110000)
  upper := (12163211/332110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_41_interval
}

theorem G21_42_formula : baezDuarteGramEntry 21 42 = vasyuninBEntry 21 42 := vasyuninBEntry_correct_axiom 21 42

theorem vasyuninBEntry_21_42_eval :
    ((((16185863/441370000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 42) ∧
    (vasyuninBEntry 21 42 ≤ (((16274137/441370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 21 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 21)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 21)
  constructor <;> linarith

theorem G21_42_interval :
    ((((16185863/441370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 42) ∧
    (baezDuarteGramEntry 21 42 ≤ (((16274137/441370000) : ℚ) : ℝ)) := by
  rw [G21_42_formula]
  exact vasyuninBEntry_21_42_eval

def interval_21_42 : NamedVasyuninInterval :=
{
  h := 21
  k := 42
  lower := (16185863/441370000)
  upper := (16274137/441370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_42_interval
}

theorem G21_43_formula : baezDuarteGramEntry 21 43 = vasyuninBEntry 21 43 := vasyuninBEntry_correct_axiom 21 43

theorem vasyuninBEntry_21_43_eval :
    ((((13950533/394670000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 43) ∧
    (vasyuninBEntry 21 43 ≤ (((14029467/394670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2143_formula_bound
  constructor <;> linarith

theorem G21_43_interval :
    ((((13950533/394670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 43) ∧
    (baezDuarteGramEntry 21 43 ≤ (((14029467/394670000) : ℚ) : ℝ)) := by
  rw [G21_43_formula]
  exact vasyuninBEntry_21_43_eval

def interval_21_43 : NamedVasyuninInterval :=
{
  h := 21
  k := 43
  lower := (13950533/394670000)
  upper := (14029467/394670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_43_interval
}

theorem G21_44_formula : baezDuarteGramEntry 21 44 = vasyuninBEntry 21 44 := vasyuninBEntry_correct_axiom 21 44

theorem vasyuninBEntry_21_44_eval :
    ((((19782547/574530000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 44) ∧
    (vasyuninBEntry 21 44 ≤ (((19897453/574530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2144_formula_bound
  constructor <;> linarith

theorem G21_44_interval :
    ((((19782547/574530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 44) ∧
    (baezDuarteGramEntry 21 44 ≤ (((19897453/574530000) : ℚ) : ℝ)) := by
  rw [G21_44_formula]
  exact vasyuninBEntry_21_44_eval

def interval_21_44 : NamedVasyuninInterval :=
{
  h := 21
  k := 44
  lower := (19782547/574530000)
  upper := (19897453/574530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_44_interval
}

theorem G21_45_formula : baezDuarteGramEntry 21 45 = vasyuninBEntry 21 45 := vasyuninBEntry_correct_axiom 21 45

theorem vasyuninBEntry_21_45_eval :
    ((((28874263/857370000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 45) ∧
    (vasyuninBEntry 21 45 ≤ (((29045737/857370000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 15 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_45_interval :
    ((((28874263/857370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 45) ∧
    (baezDuarteGramEntry 21 45 ≤ (((29045737/857370000) : ℚ) : ℝ)) := by
  rw [G21_45_formula]
  exact vasyuninBEntry_21_45_eval

def interval_21_45 : NamedVasyuninInterval :=
{
  h := 21
  k := 45
  lower := (28874263/857370000)
  upper := (29045737/857370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_45_interval
}

theorem G21_46_formula : baezDuarteGramEntry 21 46 = vasyuninBEntry 21 46 := vasyuninBEntry_correct_axiom 21 46

theorem vasyuninBEntry_21_46_eval :
    ((((3529309/106910000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 46) ∧
    (vasyuninBEntry 21 46 ≤ (((3550691/106910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2146_formula_bound
  constructor <;> linarith

theorem G21_46_interval :
    ((((3529309/106910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 46) ∧
    (baezDuarteGramEntry 21 46 ≤ (((3550691/106910000) : ℚ) : ℝ)) := by
  rw [G21_46_formula]
  exact vasyuninBEntry_21_46_eval

def interval_21_46 : NamedVasyuninInterval :=
{
  h := 21
  k := 46
  lower := (3529309/106910000)
  upper := (3550691/106910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_46_interval
}

theorem G21_47_formula : baezDuarteGramEntry 21 47 = vasyuninBEntry 21 47 := vasyuninBEntry_correct_axiom 21 47

theorem vasyuninBEntry_21_47_eval :
    ((((1186341/36590000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 47) ∧
    (vasyuninBEntry 21 47 ≤ (((1193659/36590000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2147_formula_bound
  constructor <;> linarith

theorem G21_47_interval :
    ((((1186341/36590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 47) ∧
    (baezDuarteGramEntry 21 47 ≤ (((1193659/36590000) : ℚ) : ℝ)) := by
  rw [G21_47_formula]
  exact vasyuninBEntry_21_47_eval

def interval_21_47 : NamedVasyuninInterval :=
{
  h := 21
  k := 47
  lower := (1186341/36590000)
  upper := (1193659/36590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_47_interval
}

theorem G21_48_formula : baezDuarteGramEntry 21 48 = vasyuninBEntry 21 48 := vasyuninBEntry_correct_axiom 21 48

theorem vasyuninBEntry_21_48_eval :
    ((((1043527/32730000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 48) ∧
    (vasyuninBEntry 21 48 ≤ (((1050073/32730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_7_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 7 16 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G21_48_interval :
    ((((1043527/32730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 48) ∧
    (baezDuarteGramEntry 21 48 ≤ (((1050073/32730000) : ℚ) : ℝ)) := by
  rw [G21_48_formula]
  exact vasyuninBEntry_21_48_eval

def interval_21_48 : NamedVasyuninInterval :=
{
  h := 21
  k := 48
  lower := (1043527/32730000)
  upper := (1050073/32730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_48_interval
}

theorem G21_49_formula : baezDuarteGramEntry 21 49 = vasyuninBEntry 21 49 := vasyuninBEntry_correct_axiom 21 49

theorem vasyuninBEntry_21_49_eval :
    ((((12719539/404610000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 49) ∧
    (vasyuninBEntry 21 49 ≤ (((12800461/404610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_3_7_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 3 7 7 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 7)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 7)
  constructor <;> linarith

theorem G21_49_interval :
    ((((12719539/404610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 49) ∧
    (baezDuarteGramEntry 21 49 ≤ (((12800461/404610000) : ℚ) : ℝ)) := by
  rw [G21_49_formula]
  exact vasyuninBEntry_21_49_eval

def interval_21_49 : NamedVasyuninInterval :=
{
  h := 21
  k := 49
  lower := (12719539/404610000)
  upper := (12800461/404610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_49_interval
}

theorem G21_50_formula : baezDuarteGramEntry 21 50 = vasyuninBEntry 21 50 := vasyuninBEntry_correct_axiom 21 50

theorem vasyuninBEntry_21_50_eval :
    ((((7089569/229310000) : ℚ) : ℝ) ≤ vasyuninBEntry 21 50) ∧
    (vasyuninBEntry 21 50 ≤ (((7135431/229310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2150_formula_bound
  constructor <;> linarith

theorem G21_50_interval :
    ((((7089569/229310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 21 50) ∧
    (baezDuarteGramEntry 21 50 ≤ (((7135431/229310000) : ℚ) : ℝ)) := by
  rw [G21_50_formula]
  exact vasyuninBEntry_21_50_eval

def interval_21_50 : NamedVasyuninInterval :=
{
  h := 21
  k := 50
  lower := (7089569/229310000)
  upper := (7135431/229310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G21_50_interval
}

theorem G22_1_formula : baezDuarteGramEntry 22 1 = vasyuninBEntry 1 22 := by
  rw [baezDuarteGramEntry_symm 22 1]
  exact G1_22_formula

theorem G22_1_interval :
    ((((7348967/60330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 1) ∧
    (baezDuarteGramEntry 22 1 ≤ (((7361033/60330000) : ℚ) : ℝ)) := by
  rw [G22_1_formula]
  exact vasyuninBEntry_1_22_eval

def interval_22_1 : NamedVasyuninInterval :=
{
  h := 22
  k := 1
  lower := (7348967/60330000)
  upper := (7361033/60330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_1_interval
}

theorem G22_2_formula : baezDuarteGramEntry 22 2 = vasyuninBEntry 2 22 := by
  rw [baezDuarteGramEntry_symm 22 2]
  exact G2_22_formula

theorem G22_2_interval :
    ((((47010793/442070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 2) ∧
    (baezDuarteGramEntry 22 2 ≤ (((47099207/442070000) : ℚ) : ℝ)) := by
  rw [G22_2_formula]
  exact vasyuninBEntry_2_22_eval

def interval_22_2 : NamedVasyuninInterval :=
{
  h := 22
  k := 2
  lower := (47010793/442070000)
  upper := (47099207/442070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_2_interval
}

theorem G22_3_formula : baezDuarteGramEntry 22 3 = vasyuninBEntry 3 22 := by
  rw [baezDuarteGramEntry_symm 22 3]
  exact G3_22_formula

theorem G22_3_interval :
    ((((68828611/713890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 3) ∧
    (baezDuarteGramEntry 22 3 ≤ (((68971389/713890000) : ℚ) : ℝ)) := by
  rw [G22_3_formula]
  exact vasyuninBEntry_3_22_eval

def interval_22_3 : NamedVasyuninInterval :=
{
  h := 22
  k := 3
  lower := (68828611/713890000)
  upper := (68971389/713890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_3_interval
}

theorem G22_4_formula : baezDuarteGramEntry 22 4 = vasyuninBEntry 4 22 := by
  rw [baezDuarteGramEntry_symm 22 4]
  exact G4_22_formula

theorem G22_4_interval :
    ((((73158607/813930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 4) ∧
    (baezDuarteGramEntry 22 4 ≤ (((73321393/813930000) : ℚ) : ℝ)) := by
  rw [G22_4_formula]
  exact vasyuninBEntry_4_22_eval

def interval_22_4 : NamedVasyuninInterval :=
{
  h := 22
  k := 4
  lower := (73158607/813930000)
  upper := (73321393/813930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_4_interval
}

theorem G22_5_formula : baezDuarteGramEntry 22 5 = vasyuninBEntry 5 22 := by
  rw [baezDuarteGramEntry_symm 22 5]
  exact G5_22_formula

theorem G22_5_interval :
    ((((18870197/223030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 5) ∧
    (baezDuarteGramEntry 22 5 ≤ (((18914803/223030000) : ℚ) : ℝ)) := by
  rw [G22_5_formula]
  exact vasyuninBEntry_5_22_eval

def interval_22_5 : NamedVasyuninInterval :=
{
  h := 22
  k := 5
  lower := (18870197/223030000)
  upper := (18914803/223030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_5_interval
}

theorem G22_6_formula : baezDuarteGramEntry 22 6 = vasyuninBEntry 6 22 := by
  rw [baezDuarteGramEntry_symm 22 6]
  exact G6_22_formula

theorem G22_6_interval :
    ((((71321359/886410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 6) ∧
    (baezDuarteGramEntry 22 6 ≤ (((71498641/886410000) : ℚ) : ℝ)) := by
  rw [G22_6_formula]
  exact vasyuninBEntry_6_22_eval

def interval_22_6 : NamedVasyuninInterval :=
{
  h := 22
  k := 6
  lower := (71321359/886410000)
  upper := (71498641/886410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_6_interval
}

theorem G22_7_formula : baezDuarteGramEntry 22 7 = vasyuninBEntry 7 22 := by
  rw [baezDuarteGramEntry_symm 22 7]
  exact G7_22_formula

theorem G22_7_interval :
    ((((67792577/874230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 7) ∧
    (baezDuarteGramEntry 22 7 ≤ (((67967423/874230000) : ℚ) : ℝ)) := by
  rw [G22_7_formula]
  exact vasyuninBEntry_7_22_eval

def interval_22_7 : NamedVasyuninInterval :=
{
  h := 22
  k := 7
  lower := (67792577/874230000)
  upper := (67967423/874230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_7_interval
}

theorem G22_8_formula : baezDuarteGramEntry 22 8 = vasyuninBEntry 8 22 := by
  rw [baezDuarteGramEntry_symm 22 8]
  exact G8_22_formula

theorem G22_8_interval :
    ((((69875447/945530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 8) ∧
    (baezDuarteGramEntry 22 8 ≤ (((70064553/945530000) : ℚ) : ℝ)) := by
  rw [G22_8_formula]
  exact vasyuninBEntry_8_22_eval

def interval_22_8 : NamedVasyuninInterval :=
{
  h := 22
  k := 8
  lower := (69875447/945530000)
  upper := (70064553/945530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_8_interval
}

theorem G22_9_formula : baezDuarteGramEntry 22 9 = vasyuninBEntry 9 22 := by
  rw [baezDuarteGramEntry_symm 22 9]
  exact G9_22_formula

theorem G22_9_interval :
    ((((13487/190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 9) ∧
    (baezDuarteGramEntry 22 9 ≤ (((541/7600) : ℚ) : ℝ)) := by
  rw [G22_9_formula]
  exact vasyuninBEntry_9_22_eval

def interval_22_9 : NamedVasyuninInterval :=
{
  h := 22
  k := 9
  lower := (13487/190000)
  upper := (541/7600)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_9_interval
}

theorem G22_10_formula : baezDuarteGramEntry 22 10 = vasyuninBEntry 10 22 := by
  rw [baezDuarteGramEntry_symm 22 10]
  exact G10_22_formula

theorem G22_10_interval :
    ((((1336269/19310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 10) ∧
    (baezDuarteGramEntry 22 10 ≤ (((1340131/19310000) : ℚ) : ℝ)) := by
  rw [G22_10_formula]
  exact vasyuninBEntry_10_22_eval

def interval_22_10 : NamedVasyuninInterval :=
{
  h := 22
  k := 10
  lower := (1336269/19310000)
  upper := (1340131/19310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_10_interval
}

theorem G22_11_formula : baezDuarteGramEntry 22 11 = vasyuninBEntry 11 22 := by
  rw [baezDuarteGramEntry_symm 22 11]
  exact G11_22_formula

theorem G22_11_interval :
    ((((41151297/587030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 11) ∧
    (baezDuarteGramEntry 22 11 ≤ (((41268703/587030000) : ℚ) : ℝ)) := by
  rw [G22_11_formula]
  exact vasyuninBEntry_11_22_eval

def interval_22_11 : NamedVasyuninInterval :=
{
  h := 22
  k := 11
  lower := (41151297/587030000)
  upper := (41268703/587030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_11_interval
}

theorem G22_12_formula : baezDuarteGramEntry 22 12 = vasyuninBEntry 12 22 := by
  rw [baezDuarteGramEntry_symm 22 12]
  exact G12_22_formula

theorem G22_12_interval :
    ((((27931963/430370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 12) ∧
    (baezDuarteGramEntry 22 12 ≤ (((28018037/430370000) : ℚ) : ℝ)) := by
  rw [G22_12_formula]
  exact vasyuninBEntry_12_22_eval

def interval_22_12 : NamedVasyuninInterval :=
{
  h := 22
  k := 12
  lower := (27931963/430370000)
  upper := (28018037/430370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_12_interval
}

theorem G22_13_formula : baezDuarteGramEntry 22 13 = vasyuninBEntry 13 22 := by
  rw [baezDuarteGramEntry_symm 22 13]
  exact G13_22_formula

theorem G22_13_interval :
    ((((58376347/936530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 13) ∧
    (baezDuarteGramEntry 22 13 ≤ (((58563653/936530000) : ℚ) : ℝ)) := by
  rw [G22_13_formula]
  exact vasyuninBEntry_13_22_eval

def interval_22_13 : NamedVasyuninInterval :=
{
  h := 22
  k := 13
  lower := (58376347/936530000)
  upper := (58563653/936530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_13_interval
}

theorem G22_14_formula : baezDuarteGramEntry 22 14 = vasyuninBEntry 14 22 := by
  rw [baezDuarteGramEntry_symm 22 14]
  exact G14_22_formula

theorem G22_14_interval :
    ((((58543251/967490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 14) ∧
    (baezDuarteGramEntry 22 14 ≤ (((58736749/967490000) : ℚ) : ℝ)) := by
  rw [G22_14_formula]
  exact vasyuninBEntry_14_22_eval

def interval_22_14 : NamedVasyuninInterval :=
{
  h := 22
  k := 14
  lower := (58543251/967490000)
  upper := (58736749/967490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_14_interval
}

theorem G22_15_formula : baezDuarteGramEntry 22 15 = vasyuninBEntry 15 22 := by
  rw [baezDuarteGramEntry_symm 22 15]
  exact G15_22_formula

theorem G22_15_interval :
    ((((39662891/671090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 15) ∧
    (baezDuarteGramEntry 22 15 ≤ (((39797109/671090000) : ℚ) : ℝ)) := by
  rw [G22_15_formula]
  exact vasyuninBEntry_15_22_eval

def interval_22_15 : NamedVasyuninInterval :=
{
  h := 22
  k := 15
  lower := (39662891/671090000)
  upper := (39797109/671090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_15_interval
}

theorem G22_16_formula : baezDuarteGramEntry 22 16 = vasyuninBEntry 16 22 := by
  rw [baezDuarteGramEntry_symm 22 16]
  exact G16_22_formula

theorem G22_16_interval :
    ((((3813381/66190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 16) ∧
    (baezDuarteGramEntry 22 16 ≤ (((3826619/66190000) : ℚ) : ℝ)) := by
  rw [G22_16_formula]
  exact vasyuninBEntry_16_22_eval

def interval_22_16 : NamedVasyuninInterval :=
{
  h := 22
  k := 16
  lower := (3813381/66190000)
  upper := (3826619/66190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_16_interval
}

theorem G22_17_formula : baezDuarteGramEntry 22 17 = vasyuninBEntry 17 22 := by
  rw [baezDuarteGramEntry_symm 22 17]
  exact G17_22_formula

theorem G22_17_interval :
    ((((693773/12270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 17) ∧
    (baezDuarteGramEntry 22 17 ≤ (((696227/12270000) : ℚ) : ℝ)) := by
  rw [G22_17_formula]
  exact vasyuninBEntry_17_22_eval

def interval_22_17 : NamedVasyuninInterval :=
{
  h := 22
  k := 17
  lower := (693773/12270000)
  upper := (696227/12270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_17_interval
}

theorem G22_18_formula : baezDuarteGramEntry 22 18 = vasyuninBEntry 18 22 := by
  rw [baezDuarteGramEntry_symm 22 18]
  exact G18_22_formula

theorem G22_18_interval :
    ((((2665219/47810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 18) ∧
    (baezDuarteGramEntry 22 18 ≤ (((2674781/47810000) : ℚ) : ℝ)) := by
  rw [G22_18_formula]
  exact vasyuninBEntry_18_22_eval

def interval_22_18 : NamedVasyuninInterval :=
{
  h := 22
  k := 18
  lower := (2665219/47810000)
  upper := (2674781/47810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_18_interval
}

theorem G22_19_formula : baezDuarteGramEntry 22 19 = vasyuninBEntry 19 22 := by
  rw [baezDuarteGramEntry_symm 22 19]
  exact G19_22_formula

theorem G22_19_interval :
    ((((110893/2007500) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 19) ∧
    (baezDuarteGramEntry 22 19 ≤ (((222589/4015000) : ℚ) : ℝ)) := by
  rw [G22_19_formula]
  exact vasyuninBEntry_19_22_eval

def interval_22_19 : NamedVasyuninInterval :=
{
  h := 22
  k := 19
  lower := (110893/2007500)
  upper := (222589/4015000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_19_interval
}

theorem G22_20_formula : baezDuarteGramEntry 22 20 = vasyuninBEntry 20 22 := by
  rw [baezDuarteGramEntry_symm 22 20]
  exact G20_22_formula

theorem G22_20_interval :
    ((((39697961/720390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 20) ∧
    (baezDuarteGramEntry 22 20 ≤ (((39842039/720390000) : ℚ) : ℝ)) := by
  rw [G22_20_formula]
  exact vasyuninBEntry_20_22_eval

def interval_22_20 : NamedVasyuninInterval :=
{
  h := 22
  k := 20
  lower := (39697961/720390000)
  upper := (39842039/720390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_20_interval
}

theorem G22_21_formula : baezDuarteGramEntry 22 21 = vasyuninBEntry 21 22 := by
  rw [baezDuarteGramEntry_symm 22 21]
  exact G21_22_formula

theorem G22_21_interval :
    ((((1708483/30795000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 21) ∧
    (baezDuarteGramEntry 22 21 ≤ (((857321/15397500) : ℚ) : ℝ)) := by
  rw [G22_21_formula]
  exact vasyuninBEntry_21_22_eval

def interval_22_21 : NamedVasyuninInterval :=
{
  h := 22
  k := 21
  lower := (1708483/30795000)
  upper := (857321/15397500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_21_interval
}

theorem G22_22_formula_eq : baezDuarteGramEntry 22 22 = (1 / (22 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 22 := by norm_num
  rw [baez_duarte_diagonal_scaling 22 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G22_22_log_gamma_interval :
  ((((56511209/987910000) : ℚ) : ℝ) ≤ (1 / (22 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (22 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((56708791/987910000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 22 (by norm_num)
  constructor
  · have : ((((56511209/987910000) : ℚ) : ℝ) ≤ (1 / (22 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (22 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((56708791/987910000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G22_22_interval : ((((56511209/987910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 22) ∧ (baezDuarteGramEntry 22 22 ≤ (((56708791/987910000) : ℚ) : ℝ)) := by
  rw [G22_22_formula_eq]
  exact G22_22_log_gamma_interval

def interval_22_22 : NamedVasyuninInterval :=
{
  h := 22
  k := 22
  lower := (56511209/987910000)
  upper := (56708791/987910000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G22_22_interval
}

theorem G22_23_formula : baezDuarteGramEntry 22 23 = vasyuninBEntry 22 23 := vasyuninBEntry_correct_axiom 22 23

theorem vasyuninBEntry_22_23_eval :
    ((((13012991/245090000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 23) ∧
    (vasyuninBEntry 22 23 ≤ (((13062009/245090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2223_formula_bound
  constructor <;> linarith

theorem G22_23_interval :
    ((((13012991/245090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 23) ∧
    (baezDuarteGramEntry 22 23 ≤ (((13062009/245090000) : ℚ) : ℝ)) := by
  rw [G22_23_formula]
  exact vasyuninBEntry_22_23_eval

def interval_22_23 : NamedVasyuninInterval :=
{
  h := 22
  k := 23
  lower := (13012991/245090000)
  upper := (13062009/245090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_23_interval
}

theorem G22_24_formula : baezDuarteGramEntry 22 24 = vasyuninBEntry 22 24 := vasyuninBEntry_correct_axiom 22 24

theorem vasyuninBEntry_22_24_eval :
    ((((15369579/304210000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 24) ∧
    (vasyuninBEntry 22 24 ≤ (((15430421/304210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_12_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 12 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_24_interval :
    ((((15369579/304210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 24) ∧
    (baezDuarteGramEntry 22 24 ≤ (((15430421/304210000) : ℚ) : ℝ)) := by
  rw [G22_24_formula]
  exact vasyuninBEntry_22_24_eval

def interval_22_24 : NamedVasyuninInterval :=
{
  h := 22
  k := 24
  lower := (15369579/304210000)
  upper := (15430421/304210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_24_interval
}

theorem G22_25_formula : baezDuarteGramEntry 22 25 = vasyuninBEntry 22 25 := vasyuninBEntry_correct_axiom 22 25

theorem vasyuninBEntry_22_25_eval :
    ((((9163611/188890000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 25) ∧
    (vasyuninBEntry 22 25 ≤ (((9201389/188890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2225_formula_bound
  constructor <;> linarith

theorem G22_25_interval :
    ((((9163611/188890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 25) ∧
    (baezDuarteGramEntry 22 25 ≤ (((9201389/188890000) : ℚ) : ℝ)) := by
  rw [G22_25_formula]
  exact vasyuninBEntry_22_25_eval

def interval_22_25 : NamedVasyuninInterval :=
{
  h := 22
  k := 25
  lower := (9163611/188890000)
  upper := (9201389/188890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_25_interval
}

theorem G22_26_formula : baezDuarteGramEntry 22 26 = vasyuninBEntry 22 26 := vasyuninBEntry_correct_axiom 22 26

theorem vasyuninBEntry_22_26_eval :
    ((((13655857/291430000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 26) ∧
    (vasyuninBEntry 22 26 ≤ (((13714143/291430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_13_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 13 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_26_interval :
    ((((13655857/291430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 26) ∧
    (baezDuarteGramEntry 22 26 ≤ (((13714143/291430000) : ℚ) : ℝ)) := by
  rw [G22_26_formula]
  exact vasyuninBEntry_22_26_eval

def interval_22_26 : NamedVasyuninInterval :=
{
  h := 22
  k := 26
  lower := (13655857/291430000)
  upper := (13714143/291430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_26_interval
}

theorem G22_27_formula : baezDuarteGramEntry 22 27 = vasyuninBEntry 22 27 := vasyuninBEntry_correct_axiom 22 27

theorem vasyuninBEntry_22_27_eval :
    ((((9479139/208610000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 27) ∧
    (vasyuninBEntry 22 27 ≤ (((9520861/208610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2227_formula_bound
  constructor <;> linarith

theorem G22_27_interval :
    ((((9479139/208610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 27) ∧
    (baezDuarteGramEntry 22 27 ≤ (((9520861/208610000) : ℚ) : ℝ)) := by
  rw [G22_27_formula]
  exact vasyuninBEntry_22_27_eval

def interval_22_27 : NamedVasyuninInterval :=
{
  h := 22
  k := 27
  lower := (9479139/208610000)
  upper := (9520861/208610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_27_interval
}

theorem G22_28_formula : baezDuarteGramEntry 22 28 = vasyuninBEntry 22 28 := vasyuninBEntry_correct_axiom 22 28

theorem vasyuninBEntry_22_28_eval :
    ((((23427001/529990000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 28) ∧
    (vasyuninBEntry 22 28 ≤ (((23532999/529990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 14 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_28_interval :
    ((((23427001/529990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 28) ∧
    (baezDuarteGramEntry 22 28 ≤ (((23532999/529990000) : ℚ) : ℝ)) := by
  rw [G22_28_formula]
  exact vasyuninBEntry_22_28_eval

def interval_22_28 : NamedVasyuninInterval :=
{
  h := 22
  k := 28
  lower := (23427001/529990000)
  upper := (23532999/529990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_28_interval
}

theorem G22_29_formula : baezDuarteGramEntry 22 29 = vasyuninBEntry 22 29 := vasyuninBEntry_correct_axiom 22 29

theorem vasyuninBEntry_22_29_eval :
    ((((40506113/938870000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 29) ∧
    (vasyuninBEntry 22 29 ≤ (((40693887/938870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2229_formula_bound
  constructor <;> linarith

theorem G22_29_interval :
    ((((40506113/938870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 29) ∧
    (baezDuarteGramEntry 22 29 ≤ (((40693887/938870000) : ℚ) : ℝ)) := by
  rw [G22_29_formula]
  exact vasyuninBEntry_22_29_eval

def interval_22_29 : NamedVasyuninInterval :=
{
  h := 22
  k := 29
  lower := (40506113/938870000)
  upper := (40693887/938870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_29_interval
}

theorem G22_30_formula : baezDuarteGramEntry 22 30 = vasyuninBEntry 22 30 := vasyuninBEntry_correct_axiom 22 30

theorem vasyuninBEntry_22_30_eval :
    ((((260257/6180000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 30) ∧
    (vasyuninBEntry 22 30 ≤ (((261493/6180000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 15 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_30_interval :
    ((((260257/6180000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 30) ∧
    (baezDuarteGramEntry 22 30 ≤ (((261493/6180000) : ℚ) : ℝ)) := by
  rw [G22_30_formula]
  exact vasyuninBEntry_22_30_eval

def interval_22_30 : NamedVasyuninInterval :=
{
  h := 22
  k := 30
  lower := (260257/6180000)
  upper := (261493/6180000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_30_interval
}

theorem G22_31_formula : baezDuarteGramEntry 22 31 = vasyuninBEntry 22 31 := vasyuninBEntry_correct_axiom 22 31

theorem vasyuninBEntry_22_31_eval :
    ((((15776707/382930000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 31) ∧
    (vasyuninBEntry 22 31 ≤ (((15853293/382930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2231_formula_bound
  constructor <;> linarith

theorem G22_31_interval :
    ((((15776707/382930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 31) ∧
    (baezDuarteGramEntry 22 31 ≤ (((15853293/382930000) : ℚ) : ℝ)) := by
  rw [G22_31_formula]
  exact vasyuninBEntry_22_31_eval

def interval_22_31 : NamedVasyuninInterval :=
{
  h := 22
  k := 31
  lower := (15776707/382930000)
  upper := (15853293/382930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_31_interval
}

theorem G22_32_formula : baezDuarteGramEntry 22 32 = vasyuninBEntry 22 32 := vasyuninBEntry_correct_axiom 22 32

theorem vasyuninBEntry_22_32_eval :
    ((((10763381/266190000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 32) ∧
    (vasyuninBEntry 22 32 ≤ (((10816619/266190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 16 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_32_interval :
    ((((10763381/266190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 32) ∧
    (baezDuarteGramEntry 22 32 ≤ (((10816619/266190000) : ℚ) : ℝ)) := by
  rw [G22_32_formula]
  exact vasyuninBEntry_22_32_eval

def interval_22_32 : NamedVasyuninInterval :=
{
  h := 22
  k := 32
  lower := (10763381/266190000)
  upper := (10816619/266190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_32_interval
}

theorem G22_33_formula : baezDuarteGramEntry 22 33 = vasyuninBEntry 22 33 := vasyuninBEntry_correct_axiom 22 33

theorem vasyuninBEntry_22_33_eval :
    ((((14673317/366830000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 33) ∧
    (vasyuninBEntry 22 33 ≤ (((14746683/366830000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_2_3_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 2 3 11 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 11)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 11)
  constructor <;> linarith

theorem G22_33_interval :
    ((((14673317/366830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 33) ∧
    (baezDuarteGramEntry 22 33 ≤ (((14746683/366830000) : ℚ) : ℝ)) := by
  rw [G22_33_formula]
  exact vasyuninBEntry_22_33_eval

def interval_22_33 : NamedVasyuninInterval :=
{
  h := 22
  k := 33
  lower := (14673317/366830000)
  upper := (14746683/366830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_33_interval
}

theorem G22_34_formula : baezDuarteGramEntry 22 34 = vasyuninBEntry 22 34 := vasyuninBEntry_correct_axiom 22 34

theorem vasyuninBEntry_22_34_eval :
    ((((1791397/46030000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 34) ∧
    (vasyuninBEntry 22 34 ≤ (((1800603/46030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_17_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 17 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_34_interval :
    ((((1791397/46030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 34) ∧
    (baezDuarteGramEntry 22 34 ≤ (((1800603/46030000) : ℚ) : ℝ)) := by
  rw [G22_34_formula]
  exact vasyuninBEntry_22_34_eval

def interval_22_34 : NamedVasyuninInterval :=
{
  h := 22
  k := 34
  lower := (1791397/46030000)
  upper := (1800603/46030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_34_interval
}

theorem G22_35_formula : baezDuarteGramEntry 22 35 = vasyuninBEntry 22 35 := vasyuninBEntry_correct_axiom 22 35

theorem vasyuninBEntry_22_35_eval :
    ((((18571327/486730000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 35) ∧
    (vasyuninBEntry 22 35 ≤ (((18668673/486730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2235_formula_bound
  constructor <;> linarith

theorem G22_35_interval :
    ((((18571327/486730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 35) ∧
    (baezDuarteGramEntry 22 35 ≤ (((18668673/486730000) : ℚ) : ℝ)) := by
  rw [G22_35_formula]
  exact vasyuninBEntry_22_35_eval

def interval_22_35 : NamedVasyuninInterval :=
{
  h := 22
  k := 35
  lower := (18571327/486730000)
  upper := (18668673/486730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_35_interval
}

theorem G22_36_formula : baezDuarteGramEntry 22 36 = vasyuninBEntry 22 36 := vasyuninBEntry_correct_axiom 22 36

theorem vasyuninBEntry_22_36_eval :
    ((((16032257/427430000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 36) ∧
    (vasyuninBEntry 22 36 ≤ (((16117743/427430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_18_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 18 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_36_interval :
    ((((16032257/427430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 36) ∧
    (baezDuarteGramEntry 22 36 ≤ (((16117743/427430000) : ℚ) : ℝ)) := by
  rw [G22_36_formula]
  exact vasyuninBEntry_22_36_eval

def interval_22_36 : NamedVasyuninInterval :=
{
  h := 22
  k := 36
  lower := (16032257/427430000)
  upper := (16117743/427430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_36_interval
}

theorem G22_37_formula : baezDuarteGramEntry 22 37 = vasyuninBEntry 22 37 := vasyuninBEntry_correct_axiom 22 37

theorem vasyuninBEntry_22_37_eval :
    ((((15797233/427670000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 37) ∧
    (vasyuninBEntry 22 37 ≤ (((15882767/427670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2237_formula_bound
  constructor <;> linarith

theorem G22_37_interval :
    ((((15797233/427670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 37) ∧
    (baezDuarteGramEntry 22 37 ≤ (((15882767/427670000) : ℚ) : ℝ)) := by
  rw [G22_37_formula]
  exact vasyuninBEntry_22_37_eval

def interval_22_37 : NamedVasyuninInterval :=
{
  h := 22
  k := 37
  lower := (15797233/427670000)
  upper := (15882767/427670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_37_interval
}

theorem G22_38_formula : baezDuarteGramEntry 22 38 = vasyuninBEntry 22 38 := vasyuninBEntry_correct_axiom 22 38

theorem vasyuninBEntry_22_38_eval :
    ((((807779/22210000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 38) ∧
    (vasyuninBEntry 22 38 ≤ (((812221/22210000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_19_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 19 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_38_interval :
    ((((807779/22210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 38) ∧
    (baezDuarteGramEntry 22 38 ≤ (((812221/22210000) : ℚ) : ℝ)) := by
  rw [G22_38_formula]
  exact vasyuninBEntry_22_38_eval

def interval_22_38 : NamedVasyuninInterval :=
{
  h := 22
  k := 38
  lower := (807779/22210000)
  upper := (812221/22210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_38_interval
}

theorem G22_39_formula : baezDuarteGramEntry 22 39 = vasyuninBEntry 22 39 := vasyuninBEntry_correct_axiom 22 39

theorem vasyuninBEntry_22_39_eval :
    ((((21280701/592990000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 39) ∧
    (vasyuninBEntry 22 39 ≤ (((21399299/592990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2239_formula_bound
  constructor <;> linarith

theorem G22_39_interval :
    ((((21280701/592990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 39) ∧
    (baezDuarteGramEntry 22 39 ≤ (((21399299/592990000) : ℚ) : ℝ)) := by
  rw [G22_39_formula]
  exact vasyuninBEntry_22_39_eval

def interval_22_39 : NamedVasyuninInterval :=
{
  h := 22
  k := 39
  lower := (21280701/592990000)
  upper := (21399299/592990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_39_interval
}

theorem G22_40_formula : baezDuarteGramEntry 22 40 = vasyuninBEntry 22 40 := vasyuninBEntry_correct_axiom 22 40

theorem vasyuninBEntry_22_40_eval :
    ((((19225797/542030000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 40) ∧
    (vasyuninBEntry 22 40 ≤ (((19334203/542030000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 20 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_40_interval :
    ((((19225797/542030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 40) ∧
    (baezDuarteGramEntry 22 40 ≤ (((19334203/542030000) : ℚ) : ℝ)) := by
  rw [G22_40_formula]
  exact vasyuninBEntry_22_40_eval

def interval_22_40 : NamedVasyuninInterval :=
{
  h := 22
  k := 40
  lower := (19225797/542030000)
  upper := (19334203/542030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_40_interval
}

theorem G22_41_formula : baezDuarteGramEntry 22 41 = vasyuninBEntry 22 41 := vasyuninBEntry_correct_axiom 22 41

theorem vasyuninBEntry_22_41_eval :
    ((((27800853/791470000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 41) ∧
    (vasyuninBEntry 22 41 ≤ (((27959147/791470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2241_formula_bound
  constructor <;> linarith

theorem G22_41_interval :
    ((((27800853/791470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 41) ∧
    (baezDuarteGramEntry 22 41 ≤ (((27959147/791470000) : ℚ) : ℝ)) := by
  rw [G22_41_formula]
  exact vasyuninBEntry_22_41_eval

def interval_22_41 : NamedVasyuninInterval :=
{
  h := 22
  k := 41
  lower := (27800853/791470000)
  upper := (27959147/791470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_41_interval
}

theorem G22_42_formula : baezDuarteGramEntry 22 42 = vasyuninBEntry 22 42 := vasyuninBEntry_correct_axiom 22 42

theorem vasyuninBEntry_22_42_eval :
    ((((27700577/794230000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 42) ∧
    (vasyuninBEntry 22 42 ≤ (((27859423/794230000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 21 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_42_interval :
    ((((27700577/794230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 42) ∧
    (baezDuarteGramEntry 22 42 ≤ (((27859423/794230000) : ℚ) : ℝ)) := by
  rw [G22_42_formula]
  exact vasyuninBEntry_22_42_eval

def interval_22_42 : NamedVasyuninInterval :=
{
  h := 22
  k := 42
  lower := (27700577/794230000)
  upper := (27859423/794230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_42_interval
}

theorem G22_43_formula : baezDuarteGramEntry 22 43 = vasyuninBEntry 22 43 := vasyuninBEntry_correct_axiom 22 43

theorem vasyuninBEntry_22_43_eval :
    ((((5538069/159310000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 43) ∧
    (vasyuninBEntry 22 43 ≤ (((5569931/159310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2243_formula_bound
  constructor <;> linarith

theorem G22_43_interval :
    ((((5538069/159310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 43) ∧
    (baezDuarteGramEntry 22 43 ≤ (((5569931/159310000) : ℚ) : ℝ)) := by
  rw [G22_43_formula]
  exact vasyuninBEntry_22_43_eval

def interval_22_43 : NamedVasyuninInterval :=
{
  h := 22
  k := 43
  lower := (5538069/159310000)
  upper := (5569931/159310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_43_interval
}

theorem G22_44_formula : baezDuarteGramEntry 22 44 = vasyuninBEntry 22 44 := vasyuninBEntry_correct_axiom 22 44

theorem vasyuninBEntry_22_44_eval :
    ((((28039887/801130000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 44) ∧
    (vasyuninBEntry 22 44 ≤ (((28200113/801130000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_1_2_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 1 2 22 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 22)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 22)
  constructor <;> linarith

theorem G22_44_interval :
    ((((28039887/801130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 44) ∧
    (baezDuarteGramEntry 22 44 ≤ (((28200113/801130000) : ℚ) : ℝ)) := by
  rw [G22_44_formula]
  exact vasyuninBEntry_22_44_eval

def interval_22_44 : NamedVasyuninInterval :=
{
  h := 22
  k := 44
  lower := (28039887/801130000)
  upper := (28200113/801130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_44_interval
}

theorem G22_45_formula : baezDuarteGramEntry 22 45 = vasyuninBEntry 22 45 := vasyuninBEntry_correct_axiom 22 45

theorem vasyuninBEntry_22_45_eval :
    ((((241239/7141250) : ℚ) : ℝ) ≤ vasyuninBEntry 22 45) ∧
    (vasyuninBEntry 22 45 ≤ (((970669/28565000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2245_formula_bound
  constructor <;> linarith

theorem G22_45_interval :
    ((((241239/7141250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 45) ∧
    (baezDuarteGramEntry 22 45 ≤ (((970669/28565000) : ℚ) : ℝ)) := by
  rw [G22_45_formula]
  exact vasyuninBEntry_22_45_eval

def interval_22_45 : NamedVasyuninInterval :=
{
  h := 22
  k := 45
  lower := (241239/7141250)
  upper := (970669/28565000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_45_interval
}

theorem G22_46_formula : baezDuarteGramEntry 22 46 = vasyuninBEntry 22 46 := vasyuninBEntry_correct_axiom 22 46

theorem vasyuninBEntry_22_46_eval :
    ((((29959039/909610000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 46) ∧
    (vasyuninBEntry 22 46 ≤ (((30140961/909610000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_46_interval :
    ((((29959039/909610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 46) ∧
    (baezDuarteGramEntry 22 46 ≤ (((30140961/909610000) : ℚ) : ℝ)) := by
  rw [G22_46_formula]
  exact vasyuninBEntry_22_46_eval

def interval_22_46 : NamedVasyuninInterval :=
{
  h := 22
  k := 46
  lower := (29959039/909610000)
  upper := (30140961/909610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_46_interval
}

theorem G22_47_formula : baezDuarteGramEntry 22 47 = vasyuninBEntry 22 47 := vasyuninBEntry_correct_axiom 22 47

theorem vasyuninBEntry_22_47_eval :
    ((((9779657/303430000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 47) ∧
    (vasyuninBEntry 22 47 ≤ (((9840343/303430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2247_formula_bound
  constructor <;> linarith

theorem G22_47_interval :
    ((((9779657/303430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 47) ∧
    (baezDuarteGramEntry 22 47 ≤ (((9840343/303430000) : ℚ) : ℝ)) := by
  rw [G22_47_formula]
  exact vasyuninBEntry_22_47_eval

def interval_22_47 : NamedVasyuninInterval :=
{
  h := 22
  k := 47
  lower := (9779657/303430000)
  upper := (9840343/303430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_47_interval
}

theorem G22_48_formula : baezDuarteGramEntry 22 48 = vasyuninBEntry 22 48 := vasyuninBEntry_correct_axiom 22 48

theorem vasyuninBEntry_22_48_eval :
    ((((13851189/438110000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 48) ∧
    (vasyuninBEntry 22 48 ≤ (((13938811/438110000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 24 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_48_interval :
    ((((13851189/438110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 48) ∧
    (baezDuarteGramEntry 22 48 ≤ (((13938811/438110000) : ℚ) : ℝ)) := by
  rw [G22_48_formula]
  exact vasyuninBEntry_22_48_eval

def interval_22_48 : NamedVasyuninInterval :=
{
  h := 22
  k := 48
  lower := (13851189/438110000)
  upper := (13938811/438110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_48_interval
}

theorem G22_49_formula : baezDuarteGramEntry 22 49 = vasyuninBEntry 22 49 := vasyuninBEntry_correct_axiom 22 49

theorem vasyuninBEntry_22_49_eval :
    ((((8004233/257670000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 49) ∧
    (vasyuninBEntry 22 49 ≤ (((8055767/257670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2249_formula_bound
  constructor <;> linarith

theorem G22_49_interval :
    ((((8004233/257670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 49) ∧
    (baezDuarteGramEntry 22 49 ≤ (((8055767/257670000) : ℚ) : ℝ)) := by
  rw [G22_49_formula]
  exact vasyuninBEntry_22_49_eval

def interval_22_49 : NamedVasyuninInterval :=
{
  h := 22
  k := 49
  lower := (8004233/257670000)
  upper := (8055767/257670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_49_interval
}

theorem G22_50_formula : baezDuarteGramEntry 22 50 = vasyuninBEntry 22 50 := vasyuninBEntry_correct_axiom 22 50

theorem vasyuninBEntry_22_50_eval :
    ((((180011/5890000) : ℚ) : ℝ) ≤ vasyuninBEntry 22 50) ∧
    (vasyuninBEntry 22 50 ≤ (((181189/5890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_11_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 11 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G22_50_interval :
    ((((180011/5890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 22 50) ∧
    (baezDuarteGramEntry 22 50 ≤ (((181189/5890000) : ℚ) : ℝ)) := by
  rw [G22_50_formula]
  exact vasyuninBEntry_22_50_eval

def interval_22_50 : NamedVasyuninInterval :=
{
  h := 22
  k := 50
  lower := (180011/5890000)
  upper := (181189/5890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G22_50_interval
}

theorem G23_1_formula : baezDuarteGramEntry 23 1 = vasyuninBEntry 1 23 := by
  rw [baezDuarteGramEntry_symm 23 1]
  exact G1_23_formula

theorem G23_1_interval :
    ((((57700879/491210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 1) ∧
    (baezDuarteGramEntry 23 1 ≤ (((57799121/491210000) : ℚ) : ℝ)) := by
  rw [G23_1_formula]
  exact vasyuninBEntry_1_23_eval

def interval_23_1 : NamedVasyuninInterval :=
{
  h := 23
  k := 1
  lower := (57700879/491210000)
  upper := (57799121/491210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_1_interval
}

theorem G23_2_formula : baezDuarteGramEntry 23 2 = vasyuninBEntry 2 23 := by
  rw [baezDuarteGramEntry_symm 23 2]
  exact G2_23_formula

theorem G23_2_interval :
    ((((100961091/989090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 2) ∧
    (baezDuarteGramEntry 23 2 ≤ (((101158909/989090000) : ℚ) : ℝ)) := by
  rw [G23_2_formula]
  exact vasyuninBEntry_2_23_eval

def interval_23_2 : NamedVasyuninInterval :=
{
  h := 23
  k := 2
  lower := (100961091/989090000)
  upper := (101158909/989090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_2_interval
}

theorem G23_3_formula : baezDuarteGramEntry 23 3 = vasyuninBEntry 3 23 := by
  rw [baezDuarteGramEntry_symm 23 3]
  exact G3_23_formula

theorem G23_3_interval :
    ((((55640283/597170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 3) ∧
    (baezDuarteGramEntry 23 3 ≤ (((55759717/597170000) : ℚ) : ℝ)) := by
  rw [G23_3_formula]
  exact vasyuninBEntry_3_23_eval

def interval_23_3 : NamedVasyuninInterval :=
{
  h := 23
  k := 3
  lower := (55640283/597170000)
  upper := (55759717/597170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_3_interval
}

theorem G23_4_formula : baezDuarteGramEntry 23 4 = vasyuninBEntry 4 23 := by
  rw [baezDuarteGramEntry_symm 23 4]
  exact G4_23_formula

theorem G23_4_interval :
    ((((1713229/19710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 4) ∧
    (baezDuarteGramEntry 23 4 ≤ (((1717171/19710000) : ℚ) : ℝ)) := by
  rw [G23_4_formula]
  exact vasyuninBEntry_4_23_eval

def interval_23_4 : NamedVasyuninInterval :=
{
  h := 23
  k := 4
  lower := (1713229/19710000)
  upper := (1717171/19710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_4_interval
}

theorem G23_5_formula : baezDuarteGramEntry 23 5 = vasyuninBEntry 5 23 := by
  rw [baezDuarteGramEntry_symm 23 5]
  exact G5_23_formula

theorem G23_5_interval :
    ((((12263023/149770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 5) ∧
    (baezDuarteGramEntry 23 5 ≤ (((12292977/149770000) : ℚ) : ℝ)) := by
  rw [G23_5_formula]
  exact vasyuninBEntry_5_23_eval

def interval_23_5 : NamedVasyuninInterval :=
{
  h := 23
  k := 5
  lower := (12263023/149770000)
  upper := (12292977/149770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_5_interval
}

theorem G23_6_formula : baezDuarteGramEntry 23 6 = vasyuninBEntry 6 23 := by
  rw [baezDuarteGramEntry_symm 23 6]
  exact G6_23_formula

theorem G23_6_interval :
    ((((75273793/962070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 6) ∧
    (baezDuarteGramEntry 23 6 ≤ (((75466207/962070000) : ℚ) : ℝ)) := by
  rw [G23_6_formula]
  exact vasyuninBEntry_6_23_eval

def interval_23_6 : NamedVasyuninInterval :=
{
  h := 23
  k := 6
  lower := (75273793/962070000)
  upper := (75466207/962070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_6_interval
}

theorem G23_7_formula : baezDuarteGramEntry 23 7 = vasyuninBEntry 7 23 := by
  rw [baezDuarteGramEntry_symm 23 7]
  exact G7_23_formula

theorem G23_7_interval :
    ((((5624463/75370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 7) ∧
    (baezDuarteGramEntry 23 7 ≤ (((5639537/75370000) : ℚ) : ℝ)) := by
  rw [G23_7_formula]
  exact vasyuninBEntry_7_23_eval

def interval_23_7 : NamedVasyuninInterval :=
{
  h := 23
  k := 7
  lower := (5624463/75370000)
  upper := (5639537/75370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_7_interval
}

theorem G23_8_formula : baezDuarteGramEntry 23 8 = vasyuninBEntry 8 23 := by
  rw [baezDuarteGramEntry_symm 23 8]
  exact G8_23_formula

theorem G23_8_interval :
    ((((909141/12590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 8) ∧
    (baezDuarteGramEntry 23 8 ≤ (((911659/12590000) : ℚ) : ℝ)) := by
  rw [G23_8_formula]
  exact vasyuninBEntry_8_23_eval

def interval_23_8 : NamedVasyuninInterval :=
{
  h := 23
  k := 8
  lower := (909141/12590000)
  upper := (911659/12590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_8_interval
}

theorem G23_9_formula : baezDuarteGramEntry 23 9 = vasyuninBEntry 9 23 := by
  rw [baezDuarteGramEntry_symm 23 9]
  exact G9_23_formula

theorem G23_9_interval :
    ((((29981449/435510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 9) ∧
    (baezDuarteGramEntry 23 9 ≤ (((30068551/435510000) : ℚ) : ℝ)) := by
  rw [G23_9_formula]
  exact vasyuninBEntry_9_23_eval

def interval_23_9 : NamedVasyuninInterval :=
{
  h := 23
  k := 9
  lower := (29981449/435510000)
  upper := (30068551/435510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_9_interval
}

theorem G23_10_formula : baezDuarteGramEntry 23 10 = vasyuninBEntry 10 23 := by
  rw [baezDuarteGramEntry_symm 23 10]
  exact G10_23_formula

theorem G23_10_interval :
    ((((60339593/904070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 10) ∧
    (baezDuarteGramEntry 23 10 ≤ (((60520407/904070000) : ℚ) : ℝ)) := by
  rw [G23_10_formula]
  exact vasyuninBEntry_10_23_eval

def interval_23_10 : NamedVasyuninInterval :=
{
  h := 23
  k := 10
  lower := (60339593/904070000)
  upper := (60520407/904070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_10_interval
}

theorem G23_11_formula : baezDuarteGramEntry 23 11 = vasyuninBEntry 11 23 := by
  rw [baezDuarteGramEntry_symm 23 11]
  exact G11_23_formula

theorem G23_11_interval :
    ((((1953439/29610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 11) ∧
    (baezDuarteGramEntry 23 11 ≤ (((1959361/29610000) : ℚ) : ℝ)) := by
  rw [G23_11_formula]
  exact vasyuninBEntry_11_23_eval

def interval_23_11 : NamedVasyuninInterval :=
{
  h := 23
  k := 11
  lower := (1953439/29610000)
  upper := (1959361/29610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_11_interval
}

theorem G23_12_formula : baezDuarteGramEntry 23 12 = vasyuninBEntry 12 23 := by
  rw [baezDuarteGramEntry_symm 23 12]
  exact G12_23_formula

theorem G23_12_interval :
    ((((42833041/669590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 12) ∧
    (baezDuarteGramEntry 23 12 ≤ (((42966959/669590000) : ℚ) : ℝ)) := by
  rw [G23_12_formula]
  exact vasyuninBEntry_12_23_eval

def interval_23_12 : NamedVasyuninInterval :=
{
  h := 23
  k := 12
  lower := (42833041/669590000)
  upper := (42966959/669590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_12_interval
}

theorem G23_13_formula : baezDuarteGramEntry 23 13 = vasyuninBEntry 13 23 := by
  rw [baezDuarteGramEntry_symm 23 13]
  exact G13_23_formula

theorem G23_13_interval :
    ((((23401551/384490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 13) ∧
    (baezDuarteGramEntry 23 13 ≤ (((23478449/384490000) : ℚ) : ℝ)) := by
  rw [G23_13_formula]
  exact vasyuninBEntry_13_23_eval

def interval_23_13 : NamedVasyuninInterval :=
{
  h := 23
  k := 13
  lower := (23401551/384490000)
  upper := (23478449/384490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_13_interval
}

theorem G23_14_formula : baezDuarteGramEntry 23 14 = vasyuninBEntry 14 23 := by
  rw [baezDuarteGramEntry_symm 23 14]
  exact G14_23_formula

theorem G23_14_interval :
    ((((38664323/656770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 14) ∧
    (baezDuarteGramEntry 23 14 ≤ (((38795677/656770000) : ℚ) : ℝ)) := by
  rw [G23_14_formula]
  exact vasyuninBEntry_14_23_eval

def interval_23_14 : NamedVasyuninInterval :=
{
  h := 23
  k := 14
  lower := (38664323/656770000)
  upper := (38795677/656770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_14_interval
}

theorem G23_15_formula : baezDuarteGramEntry 23 15 = vasyuninBEntry 15 23 := by
  rw [baezDuarteGramEntry_symm 23 15]
  exact G15_23_formula

theorem G23_15_interval :
    ((((2429273/42270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 15) ∧
    (baezDuarteGramEntry 23 15 ≤ (((2437727/42270000) : ℚ) : ℝ)) := by
  rw [G23_15_formula]
  exact vasyuninBEntry_15_23_eval

def interval_23_15 : NamedVasyuninInterval :=
{
  h := 23
  k := 15
  lower := (2429273/42270000)
  upper := (2437727/42270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_15_interval
}

theorem G23_16_formula : baezDuarteGramEntry 23 16 = vasyuninBEntry 16 23 := by
  rw [baezDuarteGramEntry_symm 23 16]
  exact G16_23_formula

theorem G23_16_interval :
    ((((36085559/644410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 16) ∧
    (baezDuarteGramEntry 23 16 ≤ (((36214441/644410000) : ℚ) : ℝ)) := by
  rw [G23_16_formula]
  exact vasyuninBEntry_16_23_eval

def interval_23_16 : NamedVasyuninInterval :=
{
  h := 23
  k := 16
  lower := (36085559/644410000)
  upper := (36214441/644410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_16_interval
}

theorem G23_17_formula : baezDuarteGramEntry 23 17 = vasyuninBEntry 17 23 := by
  rw [baezDuarteGramEntry_symm 23 17]
  exact G17_23_formula

theorem G23_17_interval :
    ((((930179/16960000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 17) ∧
    (baezDuarteGramEntry 23 17 ≤ (((933571/16960000) : ℚ) : ℝ)) := by
  rw [G23_17_formula]
  exact vasyuninBEntry_17_23_eval

def interval_23_17 : NamedVasyuninInterval :=
{
  h := 23
  k := 17
  lower := (930179/16960000)
  upper := (933571/16960000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_17_interval
}

theorem G23_18_formula : baezDuarteGramEntry 23 18 = vasyuninBEntry 18 23 := by
  rw [baezDuarteGramEntry_symm 23 18]
  exact G18_23_formula

theorem G23_18_interval :
    ((((53750251/997490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 18) ∧
    (baezDuarteGramEntry 23 18 ≤ (((53949749/997490000) : ℚ) : ℝ)) := by
  rw [G23_18_formula]
  exact vasyuninBEntry_18_23_eval

def interval_23_18 : NamedVasyuninInterval :=
{
  h := 23
  k := 18
  lower := (53750251/997490000)
  upper := (53949749/997490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_18_interval
}

theorem G23_19_formula : baezDuarteGramEntry 23 19 = vasyuninBEntry 19 23 := by
  rw [baezDuarteGramEntry_symm 23 19]
  exact G19_23_formula

theorem G23_19_interval :
    ((((11945051/224490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 19) ∧
    (baezDuarteGramEntry 23 19 ≤ (((11989949/224490000) : ℚ) : ℝ)) := by
  rw [G23_19_formula]
  exact vasyuninBEntry_19_23_eval

def interval_23_19 : NamedVasyuninInterval :=
{
  h := 23
  k := 19
  lower := (11945051/224490000)
  upper := (11989949/224490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_19_interval
}

theorem G23_20_formula : baezDuarteGramEntry 23 20 = vasyuninBEntry 20 23 := by
  rw [baezDuarteGramEntry_symm 23 20]
  exact G20_23_formula

theorem G23_20_interval :
    ((((634049/12010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 20) ∧
    (baezDuarteGramEntry 23 20 ≤ (((636451/12010000) : ℚ) : ℝ)) := by
  rw [G23_20_formula]
  exact vasyuninBEntry_20_23_eval

def interval_23_20 : NamedVasyuninInterval :=
{
  h := 23
  k := 20
  lower := (634049/12010000)
  upper := (636451/12010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_20_interval
}

theorem G23_21_formula : baezDuarteGramEntry 23 21 = vasyuninBEntry 21 23 := by
  rw [baezDuarteGramEntry_symm 23 21]
  exact G21_23_formula

theorem G23_21_interval :
    ((((50703803/961970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 21) ∧
    (baezDuarteGramEntry 23 21 ≤ (((50896197/961970000) : ℚ) : ℝ)) := by
  rw [G23_21_formula]
  exact vasyuninBEntry_21_23_eval

def interval_23_21 : NamedVasyuninInterval :=
{
  h := 23
  k := 21
  lower := (50703803/961970000)
  upper := (50896197/961970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_21_interval
}

theorem G23_22_formula : baezDuarteGramEntry 23 22 = vasyuninBEntry 22 23 := by
  rw [baezDuarteGramEntry_symm 23 22]
  exact G22_23_formula

theorem G23_22_interval :
    ((((13012991/245090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 22) ∧
    (baezDuarteGramEntry 23 22 ≤ (((13062009/245090000) : ℚ) : ℝ)) := by
  rw [G23_22_formula]
  exact vasyuninBEntry_22_23_eval

def interval_23_22 : NamedVasyuninInterval :=
{
  h := 23
  k := 22
  lower := (13012991/245090000)
  upper := (13062009/245090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_22_interval
}

theorem G23_23_formula_eq : baezDuarteGramEntry 23 23 = (1 / (23 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 23 := by norm_num
  rw [baez_duarte_diagonal_scaling 23 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G23_23_log_gamma_interval :
  ((((10455889/191110000) : ℚ) : ℝ) ≤ (1 / (23 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (23 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((10494111/191110000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 23 (by norm_num)
  constructor
  · have : ((((10455889/191110000) : ℚ) : ℝ) ≤ (1 / (23 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (23 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((10494111/191110000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G23_23_interval : ((((10455889/191110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 23) ∧ (baezDuarteGramEntry 23 23 ≤ (((10494111/191110000) : ℚ) : ℝ)) := by
  rw [G23_23_formula_eq]
  exact G23_23_log_gamma_interval

def interval_23_23 : NamedVasyuninInterval :=
{
  h := 23
  k := 23
  lower := (10455889/191110000)
  upper := (10494111/191110000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G23_23_interval
}

theorem G23_24_formula : baezDuarteGramEntry 23 24 = vasyuninBEntry 23 24 := vasyuninBEntry_correct_axiom 23 24

theorem vasyuninBEntry_23_24_eval :
    ((((21238281/417190000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 24) ∧
    (vasyuninBEntry 23 24 ≤ (((21321719/417190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2324_formula_bound
  constructor <;> linarith

theorem G23_24_interval :
    ((((21238281/417190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 24) ∧
    (baezDuarteGramEntry 23 24 ≤ (((21321719/417190000) : ℚ) : ℝ)) := by
  rw [G23_24_formula]
  exact vasyuninBEntry_23_24_eval

def interval_23_24 : NamedVasyuninInterval :=
{
  h := 23
  k := 24
  lower := (21238281/417190000)
  upper := (21321719/417190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_24_interval
}

theorem G23_25_formula : baezDuarteGramEntry 23 25 = vasyuninBEntry 23 25 := vasyuninBEntry_correct_axiom 23 25

theorem vasyuninBEntry_23_25_eval :
    ((((40755977/840230000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 25) ∧
    (vasyuninBEntry 23 25 ≤ (((40924023/840230000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2325_formula_bound
  constructor <;> linarith

theorem G23_25_interval :
    ((((40755977/840230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 25) ∧
    (baezDuarteGramEntry 23 25 ≤ (((40924023/840230000) : ℚ) : ℝ)) := by
  rw [G23_25_formula]
  exact vasyuninBEntry_23_25_eval

def interval_23_25 : NamedVasyuninInterval :=
{
  h := 23
  k := 25
  lower := (40755977/840230000)
  upper := (40924023/840230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_25_interval
}

theorem G23_26_formula : baezDuarteGramEntry 23 26 = vasyuninBEntry 23 26 := vasyuninBEntry_correct_axiom 23 26

theorem vasyuninBEntry_23_26_eval :
    ((((39984247/857530000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 26) ∧
    (vasyuninBEntry 23 26 ≤ (((40155753/857530000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2326_formula_bound
  constructor <;> linarith

theorem G23_26_interval :
    ((((39984247/857530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 26) ∧
    (baezDuarteGramEntry 23 26 ≤ (((40155753/857530000) : ℚ) : ℝ)) := by
  rw [G23_26_formula]
  exact vasyuninBEntry_23_26_eval

def interval_23_26 : NamedVasyuninInterval :=
{
  h := 23
  k := 26
  lower := (39984247/857530000)
  upper := (40155753/857530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_26_interval
}

theorem G23_27_formula : baezDuarteGramEntry 23 27 = vasyuninBEntry 23 27 := vasyuninBEntry_correct_axiom 23 27

theorem vasyuninBEntry_23_27_eval :
    ((((29235137/648630000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 27) ∧
    (vasyuninBEntry 23 27 ≤ (((29364863/648630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2327_formula_bound
  constructor <;> linarith

theorem G23_27_interval :
    ((((29235137/648630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 27) ∧
    (baezDuarteGramEntry 23 27 ≤ (((29364863/648630000) : ℚ) : ℝ)) := by
  rw [G23_27_formula]
  exact vasyuninBEntry_23_27_eval

def interval_23_27 : NamedVasyuninInterval :=
{
  h := 23
  k := 27
  lower := (29235137/648630000)
  upper := (29364863/648630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_27_interval
}

theorem G23_28_formula : baezDuarteGramEntry 23 28 = vasyuninBEntry 23 28 := vasyuninBEntry_correct_axiom 23 28

theorem vasyuninBEntry_23_28_eval :
    ((((38142789/872110000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 28) ∧
    (vasyuninBEntry 23 28 ≤ (((38317211/872110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2328_formula_bound
  constructor <;> linarith

theorem G23_28_interval :
    ((((38142789/872110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 28) ∧
    (baezDuarteGramEntry 23 28 ≤ (((38317211/872110000) : ℚ) : ℝ)) := by
  rw [G23_28_formula]
  exact vasyuninBEntry_23_28_eval

def interval_23_28 : NamedVasyuninInterval :=
{
  h := 23
  k := 28
  lower := (38142789/872110000)
  upper := (38317211/872110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_28_interval
}

theorem G23_29_formula : baezDuarteGramEntry 23 29 = vasyuninBEntry 23 29 := vasyuninBEntry_correct_axiom 23 29

theorem vasyuninBEntry_23_29_eval :
    ((((25250703/592970000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 29) ∧
    (vasyuninBEntry 23 29 ≤ (((25369297/592970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2329_formula_bound
  constructor <;> linarith

theorem G23_29_interval :
    ((((25250703/592970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 29) ∧
    (baezDuarteGramEntry 23 29 ≤ (((25369297/592970000) : ℚ) : ℝ)) := by
  rw [G23_29_formula]
  exact vasyuninBEntry_23_29_eval

def interval_23_29 : NamedVasyuninInterval :=
{
  h := 23
  k := 29
  lower := (25250703/592970000)
  upper := (25369297/592970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_29_interval
}

theorem G23_30_formula : baezDuarteGramEntry 23 30 = vasyuninBEntry 23 30 := vasyuninBEntry_correct_axiom 23 30

theorem vasyuninBEntry_23_30_eval :
    ((((40143363/966370000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 30) ∧
    (vasyuninBEntry 23 30 ≤ (((40336637/966370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2330_formula_bound
  constructor <;> linarith

theorem G23_30_interval :
    ((((40143363/966370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 30) ∧
    (baezDuarteGramEntry 23 30 ≤ (((40336637/966370000) : ℚ) : ℝ)) := by
  rw [G23_30_formula]
  exact vasyuninBEntry_23_30_eval

def interval_23_30 : NamedVasyuninInterval :=
{
  h := 23
  k := 30
  lower := (40143363/966370000)
  upper := (40336637/966370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_30_interval
}

theorem G23_31_formula : baezDuarteGramEntry 23 31 = vasyuninBEntry 23 31 := vasyuninBEntry_correct_axiom 23 31

theorem vasyuninBEntry_23_31_eval :
    ((((17816153/438470000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 31) ∧
    (vasyuninBEntry 23 31 ≤ (((17903847/438470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2331_formula_bound
  constructor <;> linarith

theorem G23_31_interval :
    ((((17816153/438470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 31) ∧
    (baezDuarteGramEntry 23 31 ≤ (((17903847/438470000) : ℚ) : ℝ)) := by
  rw [G23_31_formula]
  exact vasyuninBEntry_23_31_eval

def interval_23_31 : NamedVasyuninInterval :=
{
  h := 23
  k := 31
  lower := (17816153/438470000)
  upper := (17903847/438470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_31_interval
}

theorem G23_32_formula : baezDuarteGramEntry 23 32 = vasyuninBEntry 23 32 := vasyuninBEntry_correct_axiom 23 32

theorem vasyuninBEntry_23_32_eval :
    ((((36966953/930470000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 32) ∧
    (vasyuninBEntry 23 32 ≤ (((37153047/930470000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2332_formula_bound
  constructor <;> linarith

theorem G23_32_interval :
    ((((36966953/930470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 32) ∧
    (baezDuarteGramEntry 23 32 ≤ (((37153047/930470000) : ℚ) : ℝ)) := by
  rw [G23_32_formula]
  exact vasyuninBEntry_23_32_eval

def interval_23_32 : NamedVasyuninInterval :=
{
  h := 23
  k := 32
  lower := (36966953/930470000)
  upper := (37153047/930470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_32_interval
}

theorem G23_33_formula : baezDuarteGramEntry 23 33 = vasyuninBEntry 23 33 := vasyuninBEntry_correct_axiom 23 33

theorem vasyuninBEntry_23_33_eval :
    ((((1830303/46970000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 33) ∧
    (vasyuninBEntry 23 33 ≤ (((1839697/46970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2333_formula_bound
  constructor <;> linarith

theorem G23_33_interval :
    ((((1830303/46970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 33) ∧
    (baezDuarteGramEntry 23 33 ≤ (((1839697/46970000) : ℚ) : ℝ)) := by
  rw [G23_33_formula]
  exact vasyuninBEntry_23_33_eval

def interval_23_33 : NamedVasyuninInterval :=
{
  h := 23
  k := 33
  lower := (1830303/46970000)
  upper := (1839697/46970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_33_interval
}

theorem G23_34_formula : baezDuarteGramEntry 23 34 = vasyuninBEntry 23 34 := vasyuninBEntry_correct_axiom 23 34

theorem vasyuninBEntry_23_34_eval :
    ((((38350069/999310000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 34) ∧
    (vasyuninBEntry 23 34 ≤ (((38549931/999310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2334_formula_bound
  constructor <;> linarith

theorem G23_34_interval :
    ((((38350069/999310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 34) ∧
    (baezDuarteGramEntry 23 34 ≤ (((38549931/999310000) : ℚ) : ℝ)) := by
  rw [G23_34_formula]
  exact vasyuninBEntry_23_34_eval

def interval_23_34 : NamedVasyuninInterval :=
{
  h := 23
  k := 34
  lower := (38350069/999310000)
  upper := (38549931/999310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_34_interval
}

theorem G23_35_formula : baezDuarteGramEntry 23 35 = vasyuninBEntry 23 35 := vasyuninBEntry_correct_axiom 23 35

theorem vasyuninBEntry_23_35_eval :
    ((((18271511/484890000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 35) ∧
    (vasyuninBEntry 23 35 ≤ (((18368489/484890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2335_formula_bound
  constructor <;> linarith

theorem G23_35_interval :
    ((((18271511/484890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 35) ∧
    (baezDuarteGramEntry 23 35 ≤ (((18368489/484890000) : ℚ) : ℝ)) := by
  rw [G23_35_formula]
  exact vasyuninBEntry_23_35_eval

def interval_23_35 : NamedVasyuninInterval :=
{
  h := 23
  k := 35
  lower := (18271511/484890000)
  upper := (18368489/484890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_35_interval
}

theorem G23_36_formula : baezDuarteGramEntry 23 36 = vasyuninBEntry 23 36 := vasyuninBEntry_correct_axiom 23 36

theorem vasyuninBEntry_23_36_eval :
    ((((1385743/37570000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 36) ∧
    (vasyuninBEntry 23 36 ≤ (((1393257/37570000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2336_formula_bound
  constructor <;> linarith

theorem G23_36_interval :
    ((((1385743/37570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 36) ∧
    (baezDuarteGramEntry 23 36 ≤ (((1393257/37570000) : ℚ) : ℝ)) := by
  rw [G23_36_formula]
  exact vasyuninBEntry_23_36_eval

def interval_23_36 : NamedVasyuninInterval :=
{
  h := 23
  k := 36
  lower := (1385743/37570000)
  upper := (1393257/37570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_36_interval
}

theorem G23_37_formula : baezDuarteGramEntry 23 37 = vasyuninBEntry 23 37 := vasyuninBEntry_correct_axiom 23 37

theorem vasyuninBEntry_23_37_eval :
    ((((7008161/193390000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 37) ∧
    (vasyuninBEntry 23 37 ≤ (((7046839/193390000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2337_formula_bound
  constructor <;> linarith

theorem G23_37_interval :
    ((((7008161/193390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 37) ∧
    (baezDuarteGramEntry 23 37 ≤ (((7046839/193390000) : ℚ) : ℝ)) := by
  rw [G23_37_formula]
  exact vasyuninBEntry_23_37_eval

def interval_23_37 : NamedVasyuninInterval :=
{
  h := 23
  k := 37
  lower := (7008161/193390000)
  upper := (7046839/193390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_37_interval
}

theorem G23_38_formula : baezDuarteGramEntry 23 38 = vasyuninBEntry 23 38 := vasyuninBEntry_correct_axiom 23 38

theorem vasyuninBEntry_23_38_eval :
    ((((8837739/247610000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 38) ∧
    (vasyuninBEntry 23 38 ≤ (((8887261/247610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2338_formula_bound
  constructor <;> linarith

theorem G23_38_interval :
    ((((8837739/247610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 38) ∧
    (baezDuarteGramEntry 23 38 ≤ (((8887261/247610000) : ℚ) : ℝ)) := by
  rw [G23_38_formula]
  exact vasyuninBEntry_23_38_eval

def interval_23_38 : NamedVasyuninInterval :=
{
  h := 23
  k := 38
  lower := (8837739/247610000)
  upper := (8887261/247610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_38_interval
}

theorem G23_39_formula : baezDuarteGramEntry 23 39 = vasyuninBEntry 23 39 := vasyuninBEntry_correct_axiom 23 39

theorem vasyuninBEntry_23_39_eval :
    ((((26494613/753870000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 39) ∧
    (vasyuninBEntry 23 39 ≤ (((26645387/753870000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2339_formula_bound
  constructor <;> linarith

theorem G23_39_interval :
    ((((26494613/753870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 39) ∧
    (baezDuarteGramEntry 23 39 ≤ (((26645387/753870000) : ℚ) : ℝ)) := by
  rw [G23_39_formula]
  exact vasyuninBEntry_23_39_eval

def interval_23_39 : NamedVasyuninInterval :=
{
  h := 23
  k := 39
  lower := (26494613/753870000)
  upper := (26645387/753870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_39_interval
}

theorem G23_40_formula : baezDuarteGramEntry 23 40 = vasyuninBEntry 23 40 := vasyuninBEntry_correct_axiom 23 40

theorem vasyuninBEntry_23_40_eval :
    ((((161883/4670000) : ℚ) : ℝ) ≤ vasyuninBEntry 23 40) ∧
    (vasyuninBEntry 23 40 ≤ (((162817/4670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_2340_formula_bound
  constructor <;> linarith

theorem G23_40_interval :
    ((((161883/4670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 23 40) ∧
    (baezDuarteGramEntry 23 40 ≤ (((162817/4670000) : ℚ) : ℝ)) := by
  rw [G23_40_formula]
  exact vasyuninBEntry_23_40_eval

def interval_23_40 : NamedVasyuninInterval :=
{
  h := 23
  k := 40
  lower := (161883/4670000)
  upper := (162817/4670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G23_40_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
