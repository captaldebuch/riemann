import RiemannHypothesis.Criteria.NymanBeurling.VasyuninGram
import RiemannHypothesis.Certificates.Generated.VasyuninPrimitiveBoundsGenerated
import RiemannHypothesis.Criteria.NymanBeurling.VasyuninPrimitiveBounds
import Mathlib
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part1
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part2
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part3
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part4
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part5
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part6
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part7
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part8

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G37_25_formula : baezDuarteGramEntry 37 25 = vasyuninBEntry 25 37 := by
  rw [baezDuarteGramEntry_symm 37 25]
  exact G25_37_formula

theorem G37_25_interval :
    ((((20601609/583910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 25) ∧
    (baezDuarteGramEntry 37 25 ≤ (((20718391/583910000) : ℚ) : ℝ)) := by
  rw [G37_25_formula]
  exact vasyuninBEntry_25_37_eval

def interval_37_25 : NamedVasyuninInterval :=
{
  h := 37
  k := 25
  lower := (20601609/583910000)
  upper := (20718391/583910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_25_interval
}

theorem G37_26_formula : baezDuarteGramEntry 37 26 = vasyuninBEntry 26 37 := by
  rw [baezDuarteGramEntry_symm 37 26]
  exact G26_37_formula

theorem G37_26_interval :
    ((((34290977/990230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 26) ∧
    (baezDuarteGramEntry 37 26 ≤ (((34489023/990230000) : ℚ) : ℝ)) := by
  rw [G37_26_formula]
  exact vasyuninBEntry_26_37_eval

def interval_37_26 : NamedVasyuninInterval :=
{
  h := 37
  k := 26
  lower := (34290977/990230000)
  upper := (34489023/990230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_26_interval
}

theorem G37_27_formula : baezDuarteGramEntry 37 27 = vasyuninBEntry 27 37 := by
  rw [baezDuarteGramEntry_symm 37 27]
  exact G27_37_formula

theorem G37_27_interval :
    ((((6261677/183230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 27) ∧
    (baezDuarteGramEntry 37 27 ≤ (((6298323/183230000) : ℚ) : ℝ)) := by
  rw [G37_27_formula]
  exact vasyuninBEntry_27_37_eval

def interval_37_27 : NamedVasyuninInterval :=
{
  h := 37
  k := 27
  lower := (6261677/183230000)
  upper := (6298323/183230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_27_interval
}

theorem G37_28_formula : baezDuarteGramEntry 37 28 = vasyuninBEntry 28 37 := by
  rw [baezDuarteGramEntry_symm 37 28]
  exact G28_37_formula

theorem G37_28_interval :
    ((((2367003/69970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 28) ∧
    (baezDuarteGramEntry 37 28 ≤ (((2380997/69970000) : ℚ) : ℝ)) := by
  rw [G37_28_formula]
  exact vasyuninBEntry_28_37_eval

def interval_37_28 : NamedVasyuninInterval :=
{
  h := 37
  k := 28
  lower := (2367003/69970000)
  upper := (2380997/69970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_28_interval
}

theorem G37_29_formula : baezDuarteGramEntry 37 29 = vasyuninBEntry 29 37 := by
  rw [baezDuarteGramEntry_symm 37 29]
  exact G29_37_formula

theorem G37_29_interval :
    ((((33160849/991510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 29) ∧
    (baezDuarteGramEntry 37 29 ≤ (((33359151/991510000) : ℚ) : ℝ)) := by
  rw [G37_29_formula]
  exact vasyuninBEntry_29_37_eval

def interval_37_29 : NamedVasyuninInterval :=
{
  h := 37
  k := 29
  lower := (33160849/991510000)
  upper := (33359151/991510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_29_interval
}

theorem G37_30_formula : baezDuarteGramEntry 37 30 = vasyuninBEntry 30 37 := by
  rw [baezDuarteGramEntry_symm 37 30]
  exact G30_37_formula

theorem G37_30_interval :
    ((((14600983/440170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 30) ∧
    (baezDuarteGramEntry 37 30 ≤ (((14689017/440170000) : ℚ) : ℝ)) := by
  rw [G37_30_formula]
  exact vasyuninBEntry_30_37_eval

def interval_37_30 : NamedVasyuninInterval :=
{
  h := 37
  k := 30
  lower := (14600983/440170000)
  upper := (14689017/440170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_30_interval
}

theorem G37_31_formula : baezDuarteGramEntry 37 31 = vasyuninBEntry 31 37 := by
  rw [baezDuarteGramEntry_symm 37 31]
  exact G31_37_formula

theorem G37_31_interval :
    ((((27466657/833430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 31) ∧
    (baezDuarteGramEntry 37 31 ≤ (((27633343/833430000) : ℚ) : ℝ)) := by
  rw [G37_31_formula]
  exact vasyuninBEntry_31_37_eval

def interval_37_31 : NamedVasyuninInterval :=
{
  h := 37
  k := 31
  lower := (27466657/833430000)
  upper := (27633343/833430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_31_interval
}

theorem G37_32_formula : baezDuarteGramEntry 37 32 = vasyuninBEntry 32 37 := by
  rw [baezDuarteGramEntry_symm 37 32]
  exact G32_37_formula

theorem G37_32_interval :
    ((((15652277/477230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 32) ∧
    (baezDuarteGramEntry 37 32 ≤ (((15747723/477230000) : ℚ) : ℝ)) := by
  rw [G37_32_formula]
  exact vasyuninBEntry_32_37_eval

def interval_37_32 : NamedVasyuninInterval :=
{
  h := 37
  k := 32
  lower := (15652277/477230000)
  upper := (15747723/477230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_32_interval
}

theorem G37_33_formula : baezDuarteGramEntry 37 33 = vasyuninBEntry 33 37 := by
  rw [baezDuarteGramEntry_symm 37 33]
  exact G33_37_formula

theorem G37_33_interval :
    ((((12481857/381430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 33) ∧
    (baezDuarteGramEntry 37 33 ≤ (((12558143/381430000) : ℚ) : ℝ)) := by
  rw [G37_33_formula]
  exact vasyuninBEntry_33_37_eval

def interval_37_33 : NamedVasyuninInterval :=
{
  h := 37
  k := 33
  lower := (12481857/381430000)
  upper := (12558143/381430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_33_interval
}

theorem G37_34_formula : baezDuarteGramEntry 37 34 = vasyuninBEntry 34 37 := by
  rw [baezDuarteGramEntry_symm 37 34]
  exact G34_37_formula

theorem G37_34_interval :
    ((((30606513/934870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 34) ∧
    (baezDuarteGramEntry 37 34 ≤ (((30793487/934870000) : ℚ) : ℝ)) := by
  rw [G37_34_formula]
  exact vasyuninBEntry_34_37_eval

def interval_37_34 : NamedVasyuninInterval :=
{
  h := 37
  k := 34
  lower := (30606513/934870000)
  upper := (30793487/934870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_34_interval
}

theorem G37_35_formula : baezDuarteGramEntry 37 35 = vasyuninBEntry 35 37 := by
  rw [baezDuarteGramEntry_symm 37 35]
  exact G35_37_formula

theorem G37_35_interval :
    ((((17975317/546830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 35) ∧
    (baezDuarteGramEntry 37 35 ≤ (((18084683/546830000) : ℚ) : ℝ)) := by
  rw [G37_35_formula]
  exact vasyuninBEntry_35_37_eval

def interval_37_35 : NamedVasyuninInterval :=
{
  h := 37
  k := 35
  lower := (17975317/546830000)
  upper := (18084683/546830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_35_interval
}

theorem G37_36_formula : baezDuarteGramEntry 37 36 = vasyuninBEntry 36 37 := by
  rw [baezDuarteGramEntry_symm 37 36]
  exact G36_37_formula

theorem G37_36_interval :
    ((((9566171/288290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 36) ∧
    (baezDuarteGramEntry 37 36 ≤ (((9623829/288290000) : ℚ) : ℝ)) := by
  rw [G37_36_formula]
  exact vasyuninBEntry_36_37_eval

def interval_37_36 : NamedVasyuninInterval :=
{
  h := 37
  k := 36
  lower := (9566171/288290000)
  upper := (9623829/288290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_36_interval
}

theorem G37_37_formula_eq : baezDuarteGramEntry 37 37 = (1 / (37 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 37 := by norm_num
  rw [baez_duarte_diagonal_scaling 37 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G37_37_log_gamma_interval :
  ((((3051019/89810000) : ℚ) : ℝ) ≤ (1 / (37 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (37 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((3068981/89810000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 37 (by norm_num)
  constructor
  · have : ((((3051019/89810000) : ℚ) : ℝ) ≤ (1 / (37 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (37 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((3068981/89810000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G37_37_interval : ((((3051019/89810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 37) ∧ (baezDuarteGramEntry 37 37 ≤ (((3068981/89810000) : ℚ) : ℝ)) := by
  rw [G37_37_formula_eq]
  exact G37_37_log_gamma_interval

def interval_37_37 : NamedVasyuninInterval :=
{
  h := 37
  k := 37
  lower := (3051019/89810000)
  upper := (3068981/89810000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G37_37_interval
}

theorem G37_38_formula : baezDuarteGramEntry 37 38 = vasyuninBEntry 37 38 := vasyuninBEntry_correct_axiom 37 38

theorem vasyuninBEntry_37_38_eval :
    ((((1409389/43610000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 38) ∧
    (vasyuninBEntry 37 38 ≤ (((1418111/43610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3738_formula_bound
  constructor <;> linarith

theorem G37_38_interval :
    ((((1409389/43610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 38) ∧
    (baezDuarteGramEntry 37 38 ≤ (((1418111/43610000) : ℚ) : ℝ)) := by
  rw [G37_38_formula]
  exact vasyuninBEntry_37_38_eval

def interval_37_38 : NamedVasyuninInterval :=
{
  h := 37
  k := 38
  lower := (1409389/43610000)
  upper := (1418111/43610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_38_interval
}

theorem G37_39_formula : baezDuarteGramEntry 37 39 = vasyuninBEntry 37 39 := vasyuninBEntry_correct_axiom 37 39

theorem vasyuninBEntry_37_39_eval :
    ((((14448693/463070000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 39) ∧
    (vasyuninBEntry 37 39 ≤ (((14541307/463070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3739_formula_bound
  constructor <;> linarith

theorem G37_39_interval :
    ((((14448693/463070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 39) ∧
    (baezDuarteGramEntry 37 39 ≤ (((14541307/463070000) : ℚ) : ℝ)) := by
  rw [G37_39_formula]
  exact vasyuninBEntry_37_39_eval

def interval_37_39 : NamedVasyuninInterval :=
{
  h := 37
  k := 39
  lower := (14448693/463070000)
  upper := (14541307/463070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_39_interval
}

theorem G37_40_formula : baezDuarteGramEntry 37 40 = vasyuninBEntry 37 40 := vasyuninBEntry_correct_axiom 37 40

theorem vasyuninBEntry_37_40_eval :
    ((((17990611/593890000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 40) ∧
    (vasyuninBEntry 37 40 ≤ (((18109389/593890000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3740_formula_bound
  constructor <;> linarith

theorem G37_40_interval :
    ((((17990611/593890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 40) ∧
    (baezDuarteGramEntry 37 40 ≤ (((18109389/593890000) : ℚ) : ℝ)) := by
  rw [G37_40_formula]
  exact vasyuninBEntry_37_40_eval

def interval_37_40 : NamedVasyuninInterval :=
{
  h := 37
  k := 40
  lower := (17990611/593890000)
  upper := (18109389/593890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_40_interval
}

theorem G37_41_formula : baezDuarteGramEntry 37 41 = vasyuninBEntry 37 41 := vasyuninBEntry_correct_axiom 37 41

theorem vasyuninBEntry_37_41_eval :
    ((((14660331/496690000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 41) ∧
    (vasyuninBEntry 37 41 ≤ (((14759669/496690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3741_formula_bound
  constructor <;> linarith

theorem G37_41_interval :
    ((((14660331/496690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 41) ∧
    (baezDuarteGramEntry 37 41 ≤ (((14759669/496690000) : ℚ) : ℝ)) := by
  rw [G37_41_formula]
  exact vasyuninBEntry_37_41_eval

def interval_37_41 : NamedVasyuninInterval :=
{
  h := 37
  k := 41
  lower := (14660331/496690000)
  upper := (14759669/496690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_41_interval
}

theorem G37_42_formula : baezDuarteGramEntry 37 42 = vasyuninBEntry 37 42 := vasyuninBEntry_correct_axiom 37 42

theorem vasyuninBEntry_37_42_eval :
    ((((5550749/192510000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 42) ∧
    (vasyuninBEntry 37 42 ≤ (((5589251/192510000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3742_formula_bound
  constructor <;> linarith

theorem G37_42_interval :
    ((((5550749/192510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 42) ∧
    (baezDuarteGramEntry 37 42 ≤ (((5589251/192510000) : ℚ) : ℝ)) := by
  rw [G37_42_formula]
  exact vasyuninBEntry_37_42_eval

def interval_37_42 : NamedVasyuninInterval :=
{
  h := 37
  k := 42
  lower := (5550749/192510000)
  upper := (5589251/192510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_42_interval
}

theorem G37_43_formula : baezDuarteGramEntry 37 43 = vasyuninBEntry 37 43 := vasyuninBEntry_correct_axiom 37 43

theorem vasyuninBEntry_37_43_eval :
    ((((12864427/455730000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 43) ∧
    (vasyuninBEntry 37 43 ≤ (((12955573/455730000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3743_formula_bound
  constructor <;> linarith

theorem G37_43_interval :
    ((((12864427/455730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 43) ∧
    (baezDuarteGramEntry 37 43 ≤ (((12955573/455730000) : ℚ) : ℝ)) := by
  rw [G37_43_formula]
  exact vasyuninBEntry_37_43_eval

def interval_37_43 : NamedVasyuninInterval :=
{
  h := 37
  k := 43
  lower := (12864427/455730000)
  upper := (12955573/455730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_43_interval
}

theorem G37_44_formula : baezDuarteGramEntry 37 44 = vasyuninBEntry 37 44 := vasyuninBEntry_correct_axiom 37 44

theorem vasyuninBEntry_37_44_eval :
    ((((25657293/927070000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 44) ∧
    (vasyuninBEntry 37 44 ≤ (((25842707/927070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3744_formula_bound
  constructor <;> linarith

theorem G37_44_interval :
    ((((25657293/927070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 44) ∧
    (baezDuarteGramEntry 37 44 ≤ (((25842707/927070000) : ℚ) : ℝ)) := by
  rw [G37_44_formula]
  exact vasyuninBEntry_37_44_eval

def interval_37_44 : NamedVasyuninInterval :=
{
  h := 37
  k := 44
  lower := (25657293/927070000)
  upper := (25842707/927070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_44_interval
}

theorem G37_45_formula : baezDuarteGramEntry 37 45 = vasyuninBEntry 37 45 := vasyuninBEntry_correct_axiom 37 45

theorem vasyuninBEntry_37_45_eval :
    ((((4700201/172990000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 45) ∧
    (vasyuninBEntry 37 45 ≤ (((4734799/172990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3745_formula_bound
  constructor <;> linarith

theorem G37_45_interval :
    ((((4700201/172990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 45) ∧
    (baezDuarteGramEntry 37 45 ≤ (((4734799/172990000) : ℚ) : ℝ)) := by
  rw [G37_45_formula]
  exact vasyuninBEntry_37_45_eval

def interval_37_45 : NamedVasyuninInterval :=
{
  h := 37
  k := 45
  lower := (4700201/172990000)
  upper := (4734799/172990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_45_interval
}

theorem G37_46_formula : baezDuarteGramEntry 37 46 = vasyuninBEntry 37 46 := vasyuninBEntry_correct_axiom 37 46

theorem vasyuninBEntry_37_46_eval :
    ((((2647593/99070000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 46) ∧
    (vasyuninBEntry 37 46 ≤ (((2667407/99070000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3746_formula_bound
  constructor <;> linarith

theorem G37_46_interval :
    ((((2647593/99070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 46) ∧
    (baezDuarteGramEntry 37 46 ≤ (((2667407/99070000) : ℚ) : ℝ)) := by
  rw [G37_46_formula]
  exact vasyuninBEntry_37_46_eval

def interval_37_46 : NamedVasyuninInterval :=
{
  h := 37
  k := 46
  lower := (2647593/99070000)
  upper := (2667407/99070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_46_interval
}

theorem G37_47_formula : baezDuarteGramEntry 37 47 = vasyuninBEntry 37 47 := vasyuninBEntry_correct_axiom 37 47

theorem vasyuninBEntry_37_47_eval :
    ((((24307501/924990000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 47) ∧
    (vasyuninBEntry 37 47 ≤ (((24492499/924990000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3747_formula_bound
  constructor <;> linarith

theorem G37_47_interval :
    ((((24307501/924990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 47) ∧
    (baezDuarteGramEntry 37 47 ≤ (((24492499/924990000) : ℚ) : ℝ)) := by
  rw [G37_47_formula]
  exact vasyuninBEntry_37_47_eval

def interval_37_47 : NamedVasyuninInterval :=
{
  h := 37
  k := 47
  lower := (24307501/924990000)
  upper := (24492499/924990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_47_interval
}

theorem G37_48_formula : baezDuarteGramEntry 37 48 = vasyuninBEntry 37 48 := vasyuninBEntry_correct_axiom 37 48

theorem vasyuninBEntry_37_48_eval :
    ((((16167529/624710000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 48) ∧
    (vasyuninBEntry 37 48 ≤ (((16292471/624710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3748_formula_bound
  constructor <;> linarith

theorem G37_48_interval :
    ((((16167529/624710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 48) ∧
    (baezDuarteGramEntry 37 48 ≤ (((16292471/624710000) : ℚ) : ℝ)) := by
  rw [G37_48_formula]
  exact vasyuninBEntry_37_48_eval

def interval_37_48 : NamedVasyuninInterval :=
{
  h := 37
  k := 48
  lower := (16167529/624710000)
  upper := (16292471/624710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_48_interval
}

theorem G37_49_formula : baezDuarteGramEntry 37 49 = vasyuninBEntry 37 49 := vasyuninBEntry_correct_axiom 37 49

theorem vasyuninBEntry_37_49_eval :
    ((((22790783/892170000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 49) ∧
    (vasyuninBEntry 37 49 ≤ (((22969217/892170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3749_formula_bound
  constructor <;> linarith

theorem G37_49_interval :
    ((((22790783/892170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 49) ∧
    (baezDuarteGramEntry 37 49 ≤ (((22969217/892170000) : ℚ) : ℝ)) := by
  rw [G37_49_formula]
  exact vasyuninBEntry_37_49_eval

def interval_37_49 : NamedVasyuninInterval :=
{
  h := 37
  k := 49
  lower := (22790783/892170000)
  upper := (22969217/892170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_49_interval
}

theorem G37_50_formula : baezDuarteGramEntry 37 50 = vasyuninBEntry 37 50 := vasyuninBEntry_correct_axiom 37 50

theorem vasyuninBEntry_37_50_eval :
    ((((1245551/49490000) : ℚ) : ℝ) ≤ vasyuninBEntry 37 50) ∧
    (vasyuninBEntry 37 50 ≤ (((1255449/49490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3750_formula_bound
  constructor <;> linarith

theorem G37_50_interval :
    ((((1245551/49490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 37 50) ∧
    (baezDuarteGramEntry 37 50 ≤ (((1255449/49490000) : ℚ) : ℝ)) := by
  rw [G37_50_formula]
  exact vasyuninBEntry_37_50_eval

def interval_37_50 : NamedVasyuninInterval :=
{
  h := 37
  k := 50
  lower := (1245551/49490000)
  upper := (1255449/49490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G37_50_interval
}

theorem G38_1_formula : baezDuarteGramEntry 38 1 = vasyuninBEntry 1 38 := by
  rw [baezDuarteGramEntry_symm 38 1]
  exact G1_38_formula

theorem G38_1_interval :
    ((((24708161/318390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 1) ∧
    (baezDuarteGramEntry 38 1 ≤ (((24771839/318390000) : ℚ) : ℝ)) := by
  rw [G38_1_formula]
  exact vasyuninBEntry_1_38_eval

def interval_38_1 : NamedVasyuninInterval :=
{
  h := 38
  k := 1
  lower := (24708161/318390000)
  upper := (24771839/318390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_1_interval
}

theorem G38_2_formula : baezDuarteGramEntry 38 2 = vasyuninBEntry 2 38 := by
  rw [baezDuarteGramEntry_symm 38 2]
  exact G2_38_formula

theorem G38_2_interval :
    ((((1130851/16490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 2) ∧
    (baezDuarteGramEntry 38 2 ≤ (((1134149/16490000) : ℚ) : ℝ)) := by
  rw [G38_2_formula]
  exact vasyuninBEntry_2_38_eval

def interval_38_2 : NamedVasyuninInterval :=
{
  h := 38
  k := 2
  lower := (1130851/16490000)
  upper := (1134149/16490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_2_interval
}

theorem G38_3_formula : baezDuarteGramEntry 38 3 = vasyuninBEntry 3 38 := by
  rw [baezDuarteGramEntry_symm 38 3]
  exact G3_38_formula

theorem G38_3_interval :
    ((((42292867/671330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 3) ∧
    (baezDuarteGramEntry 38 3 ≤ (((42427133/671330000) : ℚ) : ℝ)) := by
  rw [G38_3_formula]
  exact vasyuninBEntry_3_38_eval

def interval_38_3 : NamedVasyuninInterval :=
{
  h := 38
  k := 3
  lower := (42292867/671330000)
  upper := (42427133/671330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_3_interval
}

theorem G38_4_formula : baezDuarteGramEntry 38 4 = vasyuninBEntry 4 38 := by
  rw [baezDuarteGramEntry_symm 38 4]
  exact G4_38_formula

theorem G38_4_interval :
    ((((43945793/742070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 4) ∧
    (baezDuarteGramEntry 38 4 ≤ (((44094207/742070000) : ℚ) : ℝ)) := by
  rw [G38_4_formula]
  exact vasyuninBEntry_4_38_eval

def interval_38_4 : NamedVasyuninInterval :=
{
  h := 38
  k := 4
  lower := (43945793/742070000)
  upper := (44094207/742070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_4_interval
}

theorem G38_5_formula : baezDuarteGramEntry 38 5 = vasyuninBEntry 5 38 := by
  rw [baezDuarteGramEntry_symm 38 5]
  exact G5_38_formula

theorem G38_5_interval :
    ((((49422073/879270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 5) ∧
    (baezDuarteGramEntry 38 5 ≤ (((49597927/879270000) : ℚ) : ℝ)) := by
  rw [G38_5_formula]
  exact vasyuninBEntry_5_38_eval

def interval_38_5 : NamedVasyuninInterval :=
{
  h := 38
  k := 5
  lower := (49422073/879270000)
  upper := (49597927/879270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_5_interval
}

theorem G38_6_formula : baezDuarteGramEntry 38 6 = vasyuninBEntry 6 38 := by
  rw [baezDuarteGramEntry_symm 38 6]
  exact G6_38_formula

theorem G38_6_interval :
    ((((4672321/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 6) ∧
    (baezDuarteGramEntry 38 6 ≤ (((4689679/86790000) : ℚ) : ℝ)) := by
  rw [G38_6_formula]
  exact vasyuninBEntry_6_38_eval

def interval_38_6 : NamedVasyuninInterval :=
{
  h := 38
  k := 6
  lower := (4672321/86790000)
  upper := (4689679/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_6_interval
}

theorem G38_7_formula : baezDuarteGramEntry 38 7 = vasyuninBEntry 7 38 := by
  rw [baezDuarteGramEntry_symm 38 7]
  exact G7_38_formula

theorem G38_7_interval :
    ((((31459193/608070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 7) ∧
    (baezDuarteGramEntry 38 7 ≤ (((31580807/608070000) : ℚ) : ℝ)) := by
  rw [G38_7_formula]
  exact vasyuninBEntry_7_38_eval

def interval_38_7 : NamedVasyuninInterval :=
{
  h := 38
  k := 7
  lower := (31459193/608070000)
  upper := (31580807/608070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_7_interval
}

theorem G38_8_formula : baezDuarteGramEntry 38 8 = vasyuninBEntry 8 38 := by
  rw [baezDuarteGramEntry_symm 38 8]
  exact G8_38_formula

theorem G38_8_interval :
    ((((41227603/823970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 8) ∧
    (baezDuarteGramEntry 38 8 ≤ (((41392397/823970000) : ℚ) : ℝ)) := by
  rw [G38_8_formula]
  exact vasyuninBEntry_8_38_eval

def interval_38_8 : NamedVasyuninInterval :=
{
  h := 38
  k := 8
  lower := (41227603/823970000)
  upper := (41392397/823970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_8_interval
}

theorem G38_9_formula : baezDuarteGramEntry 38 9 = vasyuninBEntry 9 38 := by
  rw [baezDuarteGramEntry_symm 38 9]
  exact G9_38_formula

theorem G38_9_interval :
    ((((2837903/58470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 9) ∧
    (baezDuarteGramEntry 38 9 ≤ (((2849597/58470000) : ℚ) : ℝ)) := by
  rw [G38_9_formula]
  exact vasyuninBEntry_9_38_eval

def interval_38_9 : NamedVasyuninInterval :=
{
  h := 38
  k := 9
  lower := (2837903/58470000)
  upper := (2849597/58470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_9_interval
}

theorem G38_10_formula : baezDuarteGramEntry 38 10 = vasyuninBEntry 10 38 := by
  rw [baezDuarteGramEntry_symm 38 10]
  exact G10_38_formula

theorem G38_10_interval :
    ((((18859987/400130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 10) ∧
    (baezDuarteGramEntry 38 10 ≤ (((18940013/400130000) : ℚ) : ℝ)) := by
  rw [G38_10_formula]
  exact vasyuninBEntry_10_38_eval

def interval_38_10 : NamedVasyuninInterval :=
{
  h := 38
  k := 10
  lower := (18859987/400130000)
  upper := (18940013/400130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_10_interval
}

theorem G38_11_formula : baezDuarteGramEntry 38 11 = vasyuninBEntry 11 38 := by
  rw [baezDuarteGramEntry_symm 38 11]
  exact G11_38_formula

theorem G38_11_interval :
    ((((528843/11570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 11) ∧
    (baezDuarteGramEntry 38 11 ≤ (((531157/11570000) : ℚ) : ℝ)) := by
  rw [G38_11_formula]
  exact vasyuninBEntry_11_38_eval

def interval_38_11 : NamedVasyuninInterval :=
{
  h := 38
  k := 11
  lower := (528843/11570000)
  upper := (531157/11570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_11_interval
}

theorem G38_12_formula : baezDuarteGramEntry 38 12 = vasyuninBEntry 12 38 := by
  rw [baezDuarteGramEntry_symm 38 12]
  exact G12_38_formula

theorem G38_12_interval :
    ((((8236647/183530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 12) ∧
    (baezDuarteGramEntry 38 12 ≤ (((8273353/183530000) : ℚ) : ℝ)) := by
  rw [G38_12_formula]
  exact vasyuninBEntry_12_38_eval

def interval_38_12 : NamedVasyuninInterval :=
{
  h := 38
  k := 12
  lower := (8236647/183530000)
  upper := (8273353/183530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_12_interval
}

theorem G38_13_formula : baezDuarteGramEntry 38 13 = vasyuninBEntry 13 38 := by
  rw [baezDuarteGramEntry_symm 38 13]
  exact G13_38_formula

theorem G38_13_interval :
    ((((20498557/464430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 13) ∧
    (baezDuarteGramEntry 38 13 ≤ (((20591443/464430000) : ℚ) : ℝ)) := by
  rw [G38_13_formula]
  exact vasyuninBEntry_13_38_eval

def interval_38_13 : NamedVasyuninInterval :=
{
  h := 38
  k := 13
  lower := (20498557/464430000)
  upper := (20591443/464430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_13_interval
}

theorem G38_14_formula : baezDuarteGramEntry 38 14 = vasyuninBEntry 14 38 := by
  rw [baezDuarteGramEntry_symm 38 14]
  exact G14_38_formula

theorem G38_14_interval :
    ((((29869709/702910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 14) ∧
    (baezDuarteGramEntry 38 14 ≤ (((30010291/702910000) : ℚ) : ℝ)) := by
  rw [G38_14_formula]
  exact vasyuninBEntry_14_38_eval

def interval_38_14 : NamedVasyuninInterval :=
{
  h := 38
  k := 14
  lower := (29869709/702910000)
  upper := (30010291/702910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_14_interval
}

theorem G38_15_formula : baezDuarteGramEntry 38 15 = vasyuninBEntry 15 38 := by
  rw [baezDuarteGramEntry_symm 38 15]
  exact G15_38_formula

theorem G38_15_interval :
    ((((31334581/754190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 15) ∧
    (baezDuarteGramEntry 38 15 ≤ (((31485419/754190000) : ℚ) : ℝ)) := by
  rw [G38_15_formula]
  exact vasyuninBEntry_15_38_eval

def interval_38_15 : NamedVasyuninInterval :=
{
  h := 38
  k := 15
  lower := (31334581/754190000)
  upper := (31485419/754190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_15_interval
}

theorem G38_16_formula : baezDuarteGramEntry 38 16 = vasyuninBEntry 16 38 := by
  rw [baezDuarteGramEntry_symm 38 16]
  exact G16_38_formula

theorem G38_16_interval :
    ((((18270097/449030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 16) ∧
    (baezDuarteGramEntry 38 16 ≤ (((18359903/449030000) : ℚ) : ℝ)) := by
  rw [G38_16_formula]
  exact vasyuninBEntry_16_38_eval

def interval_38_16 : NamedVasyuninInterval :=
{
  h := 38
  k := 16
  lower := (18270097/449030000)
  upper := (18359903/449030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_16_interval
}

theorem G38_17_formula : baezDuarteGramEntry 38 17 = vasyuninBEntry 17 38 := by
  rw [baezDuarteGramEntry_symm 38 17]
  exact G17_38_formula

theorem G38_17_interval :
    ((((201373/5020000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 17) ∧
    (baezDuarteGramEntry 38 17 ≤ (((202377/5020000) : ℚ) : ℝ)) := by
  rw [G38_17_formula]
  exact vasyuninBEntry_17_38_eval

def interval_38_17 : NamedVasyuninInterval :=
{
  h := 38
  k := 17
  lower := (201373/5020000)
  upper := (202377/5020000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_17_interval
}

theorem G38_18_formula : baezDuarteGramEntry 38 18 = vasyuninBEntry 18 38 := by
  rw [baezDuarteGramEntry_symm 38 18]
  exact G18_38_formula

theorem G38_18_interval :
    ((((12518609/313910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 18) ∧
    (baezDuarteGramEntry 38 18 ≤ (((12581391/313910000) : ℚ) : ℝ)) := by
  rw [G38_18_formula]
  exact vasyuninBEntry_18_38_eval

def interval_38_18 : NamedVasyuninInterval :=
{
  h := 38
  k := 18
  lower := (12518609/313910000)
  upper := (12581391/313910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_18_interval
}

theorem G38_19_formula : baezDuarteGramEntry 38 19 = vasyuninBEntry 19 38 := by
  rw [baezDuarteGramEntry_symm 38 19]
  exact G19_38_formula

theorem G38_19_interval :
    ((((2952717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 19) ∧
    (baezDuarteGramEntry 38 19 ≤ (((2967283/72830000) : ℚ) : ℝ)) := by
  rw [G38_19_formula]
  exact vasyuninBEntry_19_38_eval

def interval_38_19 : NamedVasyuninInterval :=
{
  h := 38
  k := 19
  lower := (2952717/72830000)
  upper := (2967283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_19_interval
}

theorem G38_20_formula : baezDuarteGramEntry 38 20 = vasyuninBEntry 20 38 := by
  rw [baezDuarteGramEntry_symm 38 20]
  exact G20_38_formula

theorem G38_20_interval :
    ((((4625461/120390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 20) ∧
    (baezDuarteGramEntry 38 20 ≤ (((4649539/120390000) : ℚ) : ℝ)) := by
  rw [G38_20_formula]
  exact vasyuninBEntry_20_38_eval

def interval_38_20 : NamedVasyuninInterval :=
{
  h := 38
  k := 20
  lower := (4625461/120390000)
  upper := (4649539/120390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_20_interval
}

theorem G38_21_formula : baezDuarteGramEntry 38 21 = vasyuninBEntry 21 38 := by
  rw [baezDuarteGramEntry_symm 38 21]
  exact G21_38_formula

theorem G38_21_interval :
    ((((30627761/822390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 21) ∧
    (baezDuarteGramEntry 38 21 ≤ (((30792239/822390000) : ℚ) : ℝ)) := by
  rw [G38_21_formula]
  exact vasyuninBEntry_21_38_eval

def interval_38_21 : NamedVasyuninInterval :=
{
  h := 38
  k := 21
  lower := (30627761/822390000)
  upper := (30792239/822390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_21_interval
}

theorem G38_22_formula : baezDuarteGramEntry 38 22 = vasyuninBEntry 22 38 := by
  rw [baezDuarteGramEntry_symm 38 22]
  exact G22_38_formula

theorem G38_22_interval :
    ((((807779/22210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 22) ∧
    (baezDuarteGramEntry 38 22 ≤ (((812221/22210000) : ℚ) : ℝ)) := by
  rw [G38_22_formula]
  exact vasyuninBEntry_22_38_eval

def interval_38_22 : NamedVasyuninInterval :=
{
  h := 38
  k := 22
  lower := (807779/22210000)
  upper := (812221/22210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_22_interval
}

theorem G38_23_formula : baezDuarteGramEntry 38 23 = vasyuninBEntry 23 38 := by
  rw [baezDuarteGramEntry_symm 38 23]
  exact G23_38_formula

theorem G38_23_interval :
    ((((8837739/247610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 23) ∧
    (baezDuarteGramEntry 38 23 ≤ (((8887261/247610000) : ℚ) : ℝ)) := by
  rw [G38_23_formula]
  exact vasyuninBEntry_23_38_eval

def interval_38_23 : NamedVasyuninInterval :=
{
  h := 38
  k := 23
  lower := (8837739/247610000)
  upper := (8887261/247610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_23_interval
}

theorem G38_24_formula : baezDuarteGramEntry 38 24 = vasyuninBEntry 24 38 := by
  rw [baezDuarteGramEntry_symm 38 24]
  exact G24_38_formula

theorem G38_24_interval :
    ((((1483271/42290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 24) ∧
    (baezDuarteGramEntry 38 24 ≤ (((1491729/42290000) : ℚ) : ℝ)) := by
  rw [G38_24_formula]
  exact vasyuninBEntry_24_38_eval

def interval_38_24 : NamedVasyuninInterval :=
{
  h := 38
  k := 24
  lower := (1483271/42290000)
  upper := (1491729/42290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_24_interval
}

theorem G38_25_formula : baezDuarteGramEntry 38 25 = vasyuninBEntry 25 38 := by
  rw [baezDuarteGramEntry_symm 38 25]
  exact G25_38_formula

theorem G38_25_interval :
    ((((22874069/659310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 25) ∧
    (baezDuarteGramEntry 38 25 ≤ (((23005931/659310000) : ℚ) : ℝ)) := by
  rw [G38_25_formula]
  exact vasyuninBEntry_25_38_eval

def interval_38_25 : NamedVasyuninInterval :=
{
  h := 38
  k := 25
  lower := (22874069/659310000)
  upper := (23005931/659310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_25_interval
}

theorem G38_26_formula : baezDuarteGramEntry 38 26 = vasyuninBEntry 26 38 := by
  rw [baezDuarteGramEntry_symm 38 26]
  exact G26_38_formula

theorem G38_26_interval :
    ((((9247891/271090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 26) ∧
    (baezDuarteGramEntry 38 26 ≤ (((9302109/271090000) : ℚ) : ℝ)) := by
  rw [G38_26_formula]
  exact vasyuninBEntry_26_38_eval

def interval_38_26 : NamedVasyuninInterval :=
{
  h := 38
  k := 26
  lower := (9247891/271090000)
  upper := (9302109/271090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_26_interval
}

theorem G38_27_formula : baezDuarteGramEntry 38 27 = vasyuninBEntry 27 38 := by
  rw [baezDuarteGramEntry_symm 38 27]
  exact G27_38_formula

theorem G38_27_interval :
    ((((5409889/161110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 27) ∧
    (baezDuarteGramEntry 38 27 ≤ (((5442111/161110000) : ℚ) : ℝ)) := by
  rw [G38_27_formula]
  exact vasyuninBEntry_27_38_eval

def interval_38_27 : NamedVasyuninInterval :=
{
  h := 38
  k := 27
  lower := (5409889/161110000)
  upper := (5442111/161110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_27_interval
}

theorem G38_28_formula : baezDuarteGramEntry 38 28 = vasyuninBEntry 28 38 := by
  rw [baezDuarteGramEntry_symm 38 28]
  exact G28_38_formula

theorem G38_28_interval :
    ((((9915119/298810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 28) ∧
    (baezDuarteGramEntry 38 28 ≤ (((9974881/298810000) : ℚ) : ℝ)) := by
  rw [G38_28_formula]
  exact vasyuninBEntry_28_38_eval

def interval_38_28 : NamedVasyuninInterval :=
{
  h := 38
  k := 28
  lower := (9915119/298810000)
  upper := (9974881/298810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_28_interval
}

theorem G38_29_formula : baezDuarteGramEntry 38 29 = vasyuninBEntry 29 38 := by
  rw [baezDuarteGramEntry_symm 38 29]
  exact G29_38_formula

theorem G38_29_interval :
    ((((30008583/914170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 29) ∧
    (baezDuarteGramEntry 38 29 ≤ (((30191417/914170000) : ℚ) : ℝ)) := by
  rw [G38_29_formula]
  exact vasyuninBEntry_29_38_eval

def interval_38_29 : NamedVasyuninInterval :=
{
  h := 38
  k := 29
  lower := (30008583/914170000)
  upper := (30191417/914170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_29_interval
}

theorem G38_30_formula : baezDuarteGramEntry 38 30 = vasyuninBEntry 30 38 := by
  rw [baezDuarteGramEntry_symm 38 30]
  exact G30_38_formula

theorem G38_30_interval :
    ((((24135749/742510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 30) ∧
    (baezDuarteGramEntry 38 30 ≤ (((24284251/742510000) : ℚ) : ℝ)) := by
  rw [G38_30_formula]
  exact vasyuninBEntry_30_38_eval

def interval_38_30 : NamedVasyuninInterval :=
{
  h := 38
  k := 30
  lower := (24135749/742510000)
  upper := (24284251/742510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_30_interval
}

theorem G38_31_formula : baezDuarteGramEntry 38 31 = vasyuninBEntry 31 38 := by
  rw [baezDuarteGramEntry_symm 38 31]
  exact G31_38_formula

theorem G38_31_interval :
    ((((2618879/81210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 31) ∧
    (baezDuarteGramEntry 38 31 ≤ (((2635121/81210000) : ℚ) : ℝ)) := by
  rw [G38_31_formula]
  exact vasyuninBEntry_31_38_eval

def interval_38_31 : NamedVasyuninInterval :=
{
  h := 38
  k := 31
  lower := (2618879/81210000)
  upper := (2635121/81210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_31_interval
}

theorem G38_32_formula : baezDuarteGramEntry 38 32 = vasyuninBEntry 32 38 := by
  rw [baezDuarteGramEntry_symm 38 32]
  exact G32_38_formula

theorem G38_32_interval :
    ((((16817533/524670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 32) ∧
    (baezDuarteGramEntry 38 32 ≤ (((16922467/524670000) : ℚ) : ℝ)) := by
  rw [G38_32_formula]
  exact vasyuninBEntry_32_38_eval

def interval_38_32 : NamedVasyuninInterval :=
{
  h := 38
  k := 32
  lower := (16817533/524670000)
  upper := (16922467/524670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_32_interval
}

theorem G38_33_formula : baezDuarteGramEntry 38 33 = vasyuninBEntry 33 38 := by
  rw [baezDuarteGramEntry_symm 38 33]
  exact G33_38_formula

theorem G38_33_interval :
    ((((4667377/146230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 33) ∧
    (baezDuarteGramEntry 38 33 ≤ (((4696623/146230000) : ℚ) : ℝ)) := by
  rw [G38_33_formula]
  exact vasyuninBEntry_33_38_eval

def interval_38_33 : NamedVasyuninInterval :=
{
  h := 38
  k := 33
  lower := (4667377/146230000)
  upper := (4696623/146230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_33_interval
}

theorem G38_34_formula : baezDuarteGramEntry 38 34 = vasyuninBEntry 34 38 := by
  rw [baezDuarteGramEntry_symm 38 34]
  exact G34_38_formula

theorem G38_34_interval :
    ((((4621493/145070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 34) ∧
    (baezDuarteGramEntry 38 34 ≤ (((4650507/145070000) : ℚ) : ℝ)) := by
  rw [G38_34_formula]
  exact vasyuninBEntry_34_38_eval

def interval_38_34 : NamedVasyuninInterval :=
{
  h := 38
  k := 34
  lower := (4621493/145070000)
  upper := (4650507/145070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_34_interval
}

theorem G38_35_formula : baezDuarteGramEntry 38 35 = vasyuninBEntry 35 38 := by
  rw [baezDuarteGramEntry_symm 38 35]
  exact G35_38_formula

theorem G38_35_interval :
    ((((25310607/793930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 35) ∧
    (baezDuarteGramEntry 38 35 ≤ (((25469393/793930000) : ℚ) : ℝ)) := by
  rw [G38_35_formula]
  exact vasyuninBEntry_35_38_eval

def interval_38_35 : NamedVasyuninInterval :=
{
  h := 38
  k := 35
  lower := (25310607/793930000)
  upper := (25469393/793930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_35_interval
}

theorem G38_36_formula : baezDuarteGramEntry 38 36 = vasyuninBEntry 36 38 := by
  rw [baezDuarteGramEntry_symm 38 36]
  exact G36_38_formula

theorem G38_36_interval :
    ((((4750163/148370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 36) ∧
    (baezDuarteGramEntry 38 36 ≤ (((4779837/148370000) : ℚ) : ℝ)) := by
  rw [G38_36_formula]
  exact vasyuninBEntry_36_38_eval

def interval_38_36 : NamedVasyuninInterval :=
{
  h := 38
  k := 36
  lower := (4750163/148370000)
  upper := (4779837/148370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_36_interval
}

theorem G38_37_formula : baezDuarteGramEntry 38 37 = vasyuninBEntry 37 38 := by
  rw [baezDuarteGramEntry_symm 38 37]
  exact G37_38_formula

theorem G38_37_interval :
    ((((1409389/43610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 37) ∧
    (baezDuarteGramEntry 38 37 ≤ (((1418111/43610000) : ℚ) : ℝ)) := by
  rw [G38_37_formula]
  exact vasyuninBEntry_37_38_eval

def interval_38_37 : NamedVasyuninInterval :=
{
  h := 38
  k := 37
  lower := (1409389/43610000)
  upper := (1418111/43610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_37_interval
}

theorem G38_38_formula_eq : baezDuarteGramEntry 38 38 = (1 / (38 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 38 := by norm_num
  rw [baez_duarte_diagonal_scaling 38 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G38_38_log_gamma_interval :
  ((((7081091/214090000) : ℚ) : ℝ) ≤ (1 / (38 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (38 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((7123909/214090000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 38 (by norm_num)
  constructor
  · have : ((((7081091/214090000) : ℚ) : ℝ) ≤ (1 / (38 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (38 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((7123909/214090000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G38_38_interval : ((((7081091/214090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 38) ∧ (baezDuarteGramEntry 38 38 ≤ (((7123909/214090000) : ℚ) : ℝ)) := by
  rw [G38_38_formula_eq]
  exact G38_38_log_gamma_interval

def interval_38_38 : NamedVasyuninInterval :=
{
  h := 38
  k := 38
  lower := (7081091/214090000)
  upper := (7123909/214090000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G38_38_interval
}

theorem G38_39_formula : baezDuarteGramEntry 38 39 = vasyuninBEntry 38 39 := vasyuninBEntry_correct_axiom 38 39

theorem vasyuninBEntry_38_39_eval :
    ((((6145489/195110000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 39) ∧
    (vasyuninBEntry 38 39 ≤ (((6184511/195110000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3839_formula_bound
  constructor <;> linarith

theorem G38_39_interval :
    ((((6145489/195110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 39) ∧
    (baezDuarteGramEntry 38 39 ≤ (((6184511/195110000) : ℚ) : ℝ)) := by
  rw [G38_39_formula]
  exact vasyuninBEntry_38_39_eval

def interval_38_39 : NamedVasyuninInterval :=
{
  h := 38
  k := 39
  lower := (6145489/195110000)
  upper := (6184511/195110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_39_interval
}

theorem G38_40_formula : baezDuarteGramEntry 38 40 = vasyuninBEntry 38 40 := vasyuninBEntry_correct_axiom 38 40

theorem vasyuninBEntry_38_40_eval :
    ((((27140809/891910000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 40) ∧
    (vasyuninBEntry 38 40 ≤ (((27319191/891910000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_19_20_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 19 20 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G38_40_interval :
    ((((27140809/891910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 40) ∧
    (baezDuarteGramEntry 38 40 ≤ (((27319191/891910000) : ℚ) : ℝ)) := by
  rw [G38_40_formula]
  exact vasyuninBEntry_38_40_eval

def interval_38_40 : NamedVasyuninInterval :=
{
  h := 38
  k := 40
  lower := (27140809/891910000)
  upper := (27319191/891910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_40_interval
}

theorem G38_41_formula : baezDuarteGramEntry 38 41 = vasyuninBEntry 38 41 := vasyuninBEntry_correct_axiom 38 41

theorem vasyuninBEntry_38_41_eval :
    ((((29460329/996710000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 41) ∧
    (vasyuninBEntry 38 41 ≤ (((29659671/996710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3841_formula_bound
  constructor <;> linarith

theorem G38_41_interval :
    ((((29460329/996710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 41) ∧
    (baezDuarteGramEntry 38 41 ≤ (((29659671/996710000) : ℚ) : ℝ)) := by
  rw [G38_41_formula]
  exact vasyuninBEntry_38_41_eval

def interval_38_41 : NamedVasyuninInterval :=
{
  h := 38
  k := 41
  lower := (29460329/996710000)
  upper := (29659671/996710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_41_interval
}

theorem G38_42_formula : baezDuarteGramEntry 38 42 = vasyuninBEntry 38 42 := vasyuninBEntry_correct_axiom 38 42

theorem vasyuninBEntry_38_42_eval :
    ((((27046127/938730000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 42) ∧
    (vasyuninBEntry 38 42 ≤ (((27233873/938730000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_19_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 19 21 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G38_42_interval :
    ((((27046127/938730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 42) ∧
    (baezDuarteGramEntry 38 42 ≤ (((27233873/938730000) : ℚ) : ℝ)) := by
  rw [G38_42_formula]
  exact vasyuninBEntry_38_42_eval

def interval_38_42 : NamedVasyuninInterval :=
{
  h := 38
  k := 42
  lower := (27046127/938730000)
  upper := (27233873/938730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_42_interval
}

theorem G38_43_formula : baezDuarteGramEntry 38 43 = vasyuninBEntry 38 43 := vasyuninBEntry_correct_axiom 38 43

theorem vasyuninBEntry_38_43_eval :
    ((((11030821/391790000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 43) ∧
    (vasyuninBEntry 38 43 ≤ (((11109179/391790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3843_formula_bound
  constructor <;> linarith

theorem G38_43_interval :
    ((((11030821/391790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 43) ∧
    (baezDuarteGramEntry 38 43 ≤ (((11109179/391790000) : ℚ) : ℝ)) := by
  rw [G38_43_formula]
  exact vasyuninBEntry_38_43_eval

def interval_38_43 : NamedVasyuninInterval :=
{
  h := 38
  k := 43
  lower := (11030821/391790000)
  upper := (11109179/391790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_43_interval
}

theorem G38_44_formula : baezDuarteGramEntry 38 44 = vasyuninBEntry 38 44 := vasyuninBEntry_correct_axiom 38 44

theorem vasyuninBEntry_38_44_eval :
    ((((442769/16060000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 44) ∧
    (vasyuninBEntry 38 44 ≤ (((445981/16060000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_19_22_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 19 22 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G38_44_interval :
    ((((442769/16060000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 44) ∧
    (baezDuarteGramEntry 38 44 ≤ (((445981/16060000) : ℚ) : ℝ)) := by
  rw [G38_44_formula]
  exact vasyuninBEntry_38_44_eval

def interval_38_44 : NamedVasyuninInterval :=
{
  h := 38
  k := 44
  lower := (442769/16060000)
  upper := (445981/16060000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_44_interval
}

theorem G38_45_formula : baezDuarteGramEntry 38 45 = vasyuninBEntry 38 45 := vasyuninBEntry_correct_axiom 38 45

theorem vasyuninBEntry_38_45_eval :
    ((((18421867/681330000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 45) ∧
    (vasyuninBEntry 38 45 ≤ (((18558133/681330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3845_formula_bound
  constructor <;> linarith

theorem G38_45_interval :
    ((((18421867/681330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 45) ∧
    (baezDuarteGramEntry 38 45 ≤ (((18558133/681330000) : ℚ) : ℝ)) := by
  rw [G38_45_formula]
  exact vasyuninBEntry_38_45_eval

def interval_38_45 : NamedVasyuninInterval :=
{
  h := 38
  k := 45
  lower := (18421867/681330000)
  upper := (18558133/681330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_45_interval
}

theorem G38_46_formula : baezDuarteGramEntry 38 46 = vasyuninBEntry 38 46 := vasyuninBEntry_correct_axiom 38 46

theorem vasyuninBEntry_38_46_eval :
    ((((7048457/265430000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 46) ∧
    (vasyuninBEntry 38 46 ≤ (((7101543/265430000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_19_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 19 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G38_46_interval :
    ((((7048457/265430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 46) ∧
    (baezDuarteGramEntry 38 46 ≤ (((7101543/265430000) : ℚ) : ℝ)) := by
  rw [G38_46_formula]
  exact vasyuninBEntry_38_46_eval

def interval_38_46 : NamedVasyuninInterval :=
{
  h := 38
  k := 46
  lower := (7048457/265430000)
  upper := (7101543/265430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_46_interval
}

theorem G38_47_formula : baezDuarteGramEntry 38 47 = vasyuninBEntry 38 47 := vasyuninBEntry_correct_axiom 38 47

theorem vasyuninBEntry_38_47_eval :
    ((((25791229/987710000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 47) ∧
    (vasyuninBEntry 38 47 ≤ (((25988771/987710000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3847_formula_bound
  constructor <;> linarith

theorem G38_47_interval :
    ((((25791229/987710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 47) ∧
    (baezDuarteGramEntry 38 47 ≤ (((25988771/987710000) : ℚ) : ℝ)) := by
  rw [G38_47_formula]
  exact vasyuninBEntry_38_47_eval

def interval_38_47 : NamedVasyuninInterval :=
{
  h := 38
  k := 47
  lower := (25791229/987710000)
  upper := (25988771/987710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_47_interval
}

theorem G38_48_formula : baezDuarteGramEntry 38 48 = vasyuninBEntry 38 48 := vasyuninBEntry_correct_axiom 38 48

theorem vasyuninBEntry_38_48_eval :
    ((((24185881/941190000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 48) ∧
    (vasyuninBEntry 38 48 ≤ (((24374119/941190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_19_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 19 24 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G38_48_interval :
    ((((24185881/941190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 48) ∧
    (baezDuarteGramEntry 38 48 ≤ (((24374119/941190000) : ℚ) : ℝ)) := by
  rw [G38_48_formula]
  exact vasyuninBEntry_38_48_eval

def interval_38_48 : NamedVasyuninInterval :=
{
  h := 38
  k := 48
  lower := (24185881/941190000)
  upper := (24374119/941190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_48_interval
}

theorem G38_49_formula : baezDuarteGramEntry 38 49 = vasyuninBEntry 38 49 := vasyuninBEntry_correct_axiom 38 49

theorem vasyuninBEntry_38_49_eval :
    ((((952237/37630000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 49) ∧
    (vasyuninBEntry 38 49 ≤ (((959763/37630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3849_formula_bound
  constructor <;> linarith

theorem G38_49_interval :
    ((((952237/37630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 49) ∧
    (baezDuarteGramEntry 38 49 ≤ (((959763/37630000) : ℚ) : ℝ)) := by
  rw [G38_49_formula]
  exact vasyuninBEntry_38_49_eval

def interval_38_49 : NamedVasyuninInterval :=
{
  h := 38
  k := 49
  lower := (952237/37630000)
  upper := (959763/37630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_49_interval
}

theorem G38_50_formula : baezDuarteGramEntry 38 50 = vasyuninBEntry 38 50 := vasyuninBEntry_correct_axiom 38 50

theorem vasyuninBEntry_38_50_eval :
    ((((850991/34090000) : ℚ) : ℝ) ≤ vasyuninBEntry 38 50) ∧
    (vasyuninBEntry 38 50 ≤ (((857809/34090000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_19_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 19 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G38_50_interval :
    ((((850991/34090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 38 50) ∧
    (baezDuarteGramEntry 38 50 ≤ (((857809/34090000) : ℚ) : ℝ)) := by
  rw [G38_50_formula]
  exact vasyuninBEntry_38_50_eval

def interval_38_50 : NamedVasyuninInterval :=
{
  h := 38
  k := 50
  lower := (850991/34090000)
  upper := (857809/34090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G38_50_interval
}

theorem G39_1_formula : baezDuarteGramEntry 39 1 = vasyuninBEntry 1 39 := by
  rw [baezDuarteGramEntry_symm 39 1]
  exact G1_39_formula

theorem G39_1_interval :
    ((((26080657/343430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 1) ∧
    (baezDuarteGramEntry 39 1 ≤ (((26149343/343430000) : ℚ) : ℝ)) := by
  rw [G39_1_formula]
  exact vasyuninBEntry_1_39_eval

def interval_39_1 : NamedVasyuninInterval :=
{
  h := 39
  k := 1
  lower := (26080657/343430000)
  upper := (26149343/343430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_1_interval
}

theorem G39_2_formula : baezDuarteGramEntry 39 2 = vasyuninBEntry 2 39 := by
  rw [baezDuarteGramEntry_symm 39 2]
  exact G2_39_formula

theorem G39_2_interval :
    ((((10803861/161390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 2) ∧
    (baezDuarteGramEntry 39 2 ≤ (((10836139/161390000) : ℚ) : ℝ)) := by
  rw [G39_2_formula]
  exact vasyuninBEntry_2_39_eval

def interval_39_2 : NamedVasyuninInterval :=
{
  h := 39
  k := 2
  lower := (10803861/161390000)
  upper := (10836139/161390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_2_interval
}

theorem G39_3_formula : baezDuarteGramEntry 39 3 = vasyuninBEntry 3 39 := by
  rw [baezDuarteGramEntry_symm 39 3]
  exact G3_39_formula

theorem G39_3_interval :
    ((((17841241/287590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 3) ∧
    (baezDuarteGramEntry 39 3 ≤ (((17898759/287590000) : ℚ) : ℝ)) := by
  rw [G39_3_formula]
  exact vasyuninBEntry_3_39_eval

def interval_39_3 : NamedVasyuninInterval :=
{
  h := 39
  k := 3
  lower := (17841241/287590000)
  upper := (17898759/287590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_3_interval
}

theorem G39_4_formula : baezDuarteGramEntry 39 4 = vasyuninBEntry 4 39 := by
  rw [baezDuarteGramEntry_symm 39 4]
  exact G4_39_formula

theorem G39_4_interval :
    ((((2680381/46190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 4) ∧
    (baezDuarteGramEntry 39 4 ≤ (((2689619/46190000) : ℚ) : ℝ)) := by
  rw [G39_4_formula]
  exact vasyuninBEntry_4_39_eval

def interval_39_4 : NamedVasyuninInterval :=
{
  h := 39
  k := 4
  lower := (2680381/46190000)
  upper := (2689619/46190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_4_interval
}

theorem G39_5_formula : baezDuarteGramEntry 39 5 = vasyuninBEntry 5 39 := by
  rw [baezDuarteGramEntry_symm 39 5]
  exact G5_39_formula

theorem G39_5_interval :
    ((((53652783/972170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 5) ∧
    (baezDuarteGramEntry 39 5 ≤ (((53847217/972170000) : ℚ) : ℝ)) := by
  rw [G39_5_formula]
  exact vasyuninBEntry_5_39_eval

def interval_39_5 : NamedVasyuninInterval :=
{
  h := 39
  k := 5
  lower := (53652783/972170000)
  upper := (53847217/972170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_5_interval
}

theorem G39_6_formula : baezDuarteGramEntry 39 6 = vasyuninBEntry 6 39 := by
  rw [baezDuarteGramEntry_symm 39 6]
  exact G6_39_formula

theorem G39_6_interval :
    ((((46761459/885410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 6) ∧
    (baezDuarteGramEntry 39 6 ≤ (((46938541/885410000) : ℚ) : ℝ)) := by
  rw [G39_6_formula]
  exact vasyuninBEntry_6_39_eval

def interval_39_6 : NamedVasyuninInterval :=
{
  h := 39
  k := 6
  lower := (46761459/885410000)
  upper := (46938541/885410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_6_interval
}

theorem G39_7_formula : baezDuarteGramEntry 39 7 = vasyuninBEntry 7 39 := by
  rw [baezDuarteGramEntry_symm 39 7]
  exact G7_39_formula

theorem G39_7_interval :
    ((((25250233/497670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 7) ∧
    (baezDuarteGramEntry 39 7 ≤ (((25349767/497670000) : ℚ) : ℝ)) := by
  rw [G39_7_formula]
  exact vasyuninBEntry_7_39_eval

def interval_39_7 : NamedVasyuninInterval :=
{
  h := 39
  k := 7
  lower := (25250233/497670000)
  upper := (25349767/497670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_7_interval
}

theorem G39_8_formula : baezDuarteGramEntry 39 8 = vasyuninBEntry 8 39 := by
  rw [baezDuarteGramEntry_symm 39 8]
  exact G8_39_formula

theorem G39_8_interval :
    ((((4020591/81590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 8) ∧
    (baezDuarteGramEntry 39 8 ≤ (((4036909/81590000) : ℚ) : ℝ)) := by
  rw [G39_8_formula]
  exact vasyuninBEntry_8_39_eval

def interval_39_8 : NamedVasyuninInterval :=
{
  h := 39
  k := 8
  lower := (4020591/81590000)
  upper := (4036909/81590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_8_interval
}

theorem G39_9_formula : baezDuarteGramEntry 39 9 = vasyuninBEntry 9 39 := by
  rw [baezDuarteGramEntry_symm 39 9]
  exact G9_39_formula

theorem G39_9_interval :
    ((((16969311/356890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 9) ∧
    (baezDuarteGramEntry 39 9 ≤ (((17040689/356890000) : ℚ) : ℝ)) := by
  rw [G39_9_formula]
  exact vasyuninBEntry_9_39_eval

def interval_39_9 : NamedVasyuninInterval :=
{
  h := 39
  k := 9
  lower := (16969311/356890000)
  upper := (17040689/356890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_9_interval
}

theorem G39_10_formula : baezDuarteGramEntry 39 10 = vasyuninBEntry 10 39 := by
  rw [baezDuarteGramEntry_symm 39 10]
  exact G10_39_formula

theorem G39_10_interval :
    ((((9280051/199490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 10) ∧
    (baezDuarteGramEntry 39 10 ≤ (((9319949/199490000) : ℚ) : ℝ)) := by
  rw [G39_10_formula]
  exact vasyuninBEntry_10_39_eval

def interval_39_10 : NamedVasyuninInterval :=
{
  h := 39
  k := 10
  lower := (9280051/199490000)
  upper := (9319949/199490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_10_interval
}

theorem G39_11_formula : baezDuarteGramEntry 39 11 = vasyuninBEntry 11 39 := by
  rw [baezDuarteGramEntry_symm 39 11]
  exact G11_39_formula

theorem G39_11_interval :
    ((((41886633/933670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 11) ∧
    (baezDuarteGramEntry 39 11 ≤ (((42073367/933670000) : ℚ) : ℝ)) := by
  rw [G39_11_formula]
  exact vasyuninBEntry_11_39_eval

def interval_39_11 : NamedVasyuninInterval :=
{
  h := 39
  k := 11
  lower := (41886633/933670000)
  upper := (42073367/933670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_11_interval
}

theorem G39_12_formula : baezDuarteGramEntry 39 12 = vasyuninBEntry 12 39 := by
  rw [baezDuarteGramEntry_symm 39 12]
  exact G12_39_formula

theorem G39_12_interval :
    ((((35309559/804410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 12) ∧
    (baezDuarteGramEntry 39 12 ≤ (((35470441/804410000) : ℚ) : ℝ)) := by
  rw [G39_12_formula]
  exact vasyuninBEntry_12_39_eval

def interval_39_12 : NamedVasyuninInterval :=
{
  h := 39
  k := 12
  lower := (35309559/804410000)
  upper := (35470441/804410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_12_interval
}

theorem G39_13_formula : baezDuarteGramEntry 39 13 = vasyuninBEntry 13 39 := by
  rw [baezDuarteGramEntry_symm 39 13]
  exact G13_39_formula

theorem G39_13_interval :
    ((((34970757/792430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 13) ∧
    (baezDuarteGramEntry 39 13 ≤ (((35129243/792430000) : ℚ) : ℝ)) := by
  rw [G39_13_formula]
  exact vasyuninBEntry_13_39_eval

def interval_39_13 : NamedVasyuninInterval :=
{
  h := 39
  k := 13
  lower := (34970757/792430000)
  upper := (35129243/792430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_13_interval
}

theorem G39_14_formula : baezDuarteGramEntry 39 14 = vasyuninBEntry 14 39 := by
  rw [baezDuarteGramEntry_symm 39 14]
  exact G14_39_formula

theorem G39_14_interval :
    ((((783129/18710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 14) ∧
    (baezDuarteGramEntry 39 14 ≤ (((786871/18710000) : ℚ) : ℝ)) := by
  rw [G39_14_formula]
  exact vasyuninBEntry_14_39_eval

def interval_39_14 : NamedVasyuninInterval :=
{
  h := 39
  k := 14
  lower := (783129/18710000)
  upper := (786871/18710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_14_interval
}

theorem G39_15_formula : baezDuarteGramEntry 39 15 = vasyuninBEntry 15 39 := by
  rw [baezDuarteGramEntry_symm 39 15]
  exact G15_39_formula

theorem G39_15_interval :
    ((((38595341/946590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 15) ∧
    (baezDuarteGramEntry 39 15 ≤ (((38784659/946590000) : ℚ) : ℝ)) := by
  rw [G39_15_formula]
  exact vasyuninBEntry_15_39_eval

def interval_39_15 : NamedVasyuninInterval :=
{
  h := 39
  k := 15
  lower := (38595341/946590000)
  upper := (38784659/946590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_15_interval
}

theorem G39_16_formula : baezDuarteGramEntry 39 16 = vasyuninBEntry 16 39 := by
  rw [baezDuarteGramEntry_symm 39 16]
  exact G16_39_formula

theorem G39_16_interval :
    ((((37994907/950930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 16) ∧
    (baezDuarteGramEntry 39 16 ≤ (((38185093/950930000) : ℚ) : ℝ)) := by
  rw [G39_16_formula]
  exact vasyuninBEntry_16_39_eval

def interval_39_16 : NamedVasyuninInterval :=
{
  h := 39
  k := 16
  lower := (37994907/950930000)
  upper := (38185093/950930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_16_interval
}

theorem G39_17_formula : baezDuarteGramEntry 39 17 = vasyuninBEntry 17 39 := by
  rw [baezDuarteGramEntry_symm 39 17]
  exact G17_39_formula

theorem G39_17_interval :
    ((((4118269/104810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 17) ∧
    (baezDuarteGramEntry 39 17 ≤ (((4139231/104810000) : ℚ) : ℝ)) := by
  rw [G39_17_formula]
  exact vasyuninBEntry_17_39_eval

def interval_39_17 : NamedVasyuninInterval :=
{
  h := 39
  k := 17
  lower := (4118269/104810000)
  upper := (4139231/104810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_17_interval
}

theorem G39_18_formula : baezDuarteGramEntry 39 18 = vasyuninBEntry 18 39 := by
  rw [baezDuarteGramEntry_symm 39 18]
  exact G18_39_formula

theorem G39_18_interval :
    ((((8106667/208330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 18) ∧
    (baezDuarteGramEntry 39 18 ≤ (((8148333/208330000) : ℚ) : ℝ)) := by
  rw [G39_18_formula]
  exact vasyuninBEntry_18_39_eval

def interval_39_18 : NamedVasyuninInterval :=
{
  h := 39
  k := 18
  lower := (8106667/208330000)
  upper := (8148333/208330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_18_interval
}

theorem G39_19_formula : baezDuarteGramEntry 39 19 = vasyuninBEntry 19 39 := by
  rw [baezDuarteGramEntry_symm 39 19]
  exact G19_39_formula

theorem G39_19_interval :
    ((((6868371/176290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 19) ∧
    (baezDuarteGramEntry 39 19 ≤ (((6903629/176290000) : ℚ) : ℝ)) := by
  rw [G39_19_formula]
  exact vasyuninBEntry_19_39_eval

def interval_39_19 : NamedVasyuninInterval :=
{
  h := 39
  k := 19
  lower := (6868371/176290000)
  upper := (6903629/176290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_19_interval
}

theorem G39_20_formula : baezDuarteGramEntry 39 20 = vasyuninBEntry 20 39 := by
  rw [baezDuarteGramEntry_symm 39 20]
  exact G20_39_formula

theorem G39_20_interval :
    ((((36454699/953010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 20) ∧
    (baezDuarteGramEntry 39 20 ≤ (((36645301/953010000) : ℚ) : ℝ)) := by
  rw [G39_20_formula]
  exact vasyuninBEntry_20_39_eval

def interval_39_20 : NamedVasyuninInterval :=
{
  h := 39
  k := 20
  lower := (36454699/953010000)
  upper := (36645301/953010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_20_interval
}

theorem G39_21_formula : baezDuarteGramEntry 39 21 = vasyuninBEntry 21 39 := by
  rw [baezDuarteGramEntry_symm 39 21]
  exact G21_39_formula

theorem G39_21_interval :
    ((((736003/19970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 21) ∧
    (baezDuarteGramEntry 39 21 ≤ (((739997/19970000) : ℚ) : ℝ)) := by
  rw [G39_21_formula]
  exact vasyuninBEntry_21_39_eval

def interval_39_21 : NamedVasyuninInterval :=
{
  h := 39
  k := 21
  lower := (736003/19970000)
  upper := (739997/19970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_21_interval
}

theorem G39_22_formula : baezDuarteGramEntry 39 22 = vasyuninBEntry 22 39 := by
  rw [baezDuarteGramEntry_symm 39 22]
  exact G22_39_formula

theorem G39_22_interval :
    ((((21280701/592990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 22) ∧
    (baezDuarteGramEntry 39 22 ≤ (((21399299/592990000) : ℚ) : ℝ)) := by
  rw [G39_22_formula]
  exact vasyuninBEntry_22_39_eval

def interval_39_22 : NamedVasyuninInterval :=
{
  h := 39
  k := 22
  lower := (21280701/592990000)
  upper := (21399299/592990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_22_interval
}

theorem G39_23_formula : baezDuarteGramEntry 39 23 = vasyuninBEntry 23 39 := by
  rw [baezDuarteGramEntry_symm 39 23]
  exact G23_39_formula

theorem G39_23_interval :
    ((((26494613/753870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 23) ∧
    (baezDuarteGramEntry 39 23 ≤ (((26645387/753870000) : ℚ) : ℝ)) := by
  rw [G39_23_formula]
  exact vasyuninBEntry_23_39_eval

def interval_39_23 : NamedVasyuninInterval :=
{
  h := 39
  k := 23
  lower := (26494613/753870000)
  upper := (26645387/753870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_23_interval
}

theorem G39_24_formula : baezDuarteGramEntry 39 24 = vasyuninBEntry 24 39 := by
  rw [baezDuarteGramEntry_symm 39 24]
  exact G24_39_formula

theorem G39_24_interval :
    ((((18207249/527510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 24) ∧
    (baezDuarteGramEntry 39 24 ≤ (((18312751/527510000) : ℚ) : ℝ)) := by
  rw [G39_24_formula]
  exact vasyuninBEntry_24_39_eval

def interval_39_24 : NamedVasyuninInterval :=
{
  h := 39
  k := 24
  lower := (18207249/527510000)
  upper := (18312751/527510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_24_interval
}

theorem G39_25_formula : baezDuarteGramEntry 39 25 = vasyuninBEntry 25 39 := by
  rw [baezDuarteGramEntry_symm 39 25]
  exact G25_39_formula

theorem G39_25_interval :
    ((((32354849/951510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 25) ∧
    (baezDuarteGramEntry 39 25 ≤ (((32545151/951510000) : ℚ) : ℝ)) := by
  rw [G39_25_formula]
  exact vasyuninBEntry_25_39_eval

def interval_39_25 : NamedVasyuninInterval :=
{
  h := 39
  k := 25
  lower := (32354849/951510000)
  upper := (32545151/951510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_25_interval
}

theorem G39_26_formula : baezDuarteGramEntry 39 26 = vasyuninBEntry 26 39 := by
  rw [baezDuarteGramEntry_symm 39 26]
  exact G26_39_formula

theorem G39_26_interval :
    ((((20319937/600630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 26) ∧
    (baezDuarteGramEntry 39 26 ≤ (((20440063/600630000) : ℚ) : ℝ)) := by
  rw [G39_26_formula]
  exact vasyuninBEntry_26_39_eval

def interval_39_26 : NamedVasyuninInterval :=
{
  h := 39
  k := 26
  lower := (20319937/600630000)
  upper := (20440063/600630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_26_interval
}

theorem G39_27_formula : baezDuarteGramEntry 39 27 = vasyuninBEntry 27 39 := by
  rw [baezDuarteGramEntry_symm 39 27]
  exact G27_39_formula

theorem G39_27_interval :
    ((((5642929/170710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 27) ∧
    (baezDuarteGramEntry 39 27 ≤ (((5677071/170710000) : ℚ) : ℝ)) := by
  rw [G39_27_formula]
  exact vasyuninBEntry_27_39_eval

def interval_39_27 : NamedVasyuninInterval :=
{
  h := 39
  k := 27
  lower := (5642929/170710000)
  upper := (5677071/170710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_27_interval
}

theorem G39_28_formula : baezDuarteGramEntry 39 28 = vasyuninBEntry 28 39 := by
  rw [baezDuarteGramEntry_symm 39 28]
  exact G28_39_formula

theorem G39_28_interval :
    ((((30426651/933490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 28) ∧
    (baezDuarteGramEntry 39 28 ≤ (((30613349/933490000) : ℚ) : ℝ)) := by
  rw [G39_28_formula]
  exact vasyuninBEntry_28_39_eval

def interval_39_28 : NamedVasyuninInterval :=
{
  h := 39
  k := 28
  lower := (30426651/933490000)
  upper := (30613349/933490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_28_interval
}

theorem G39_29_formula : baezDuarteGramEntry 39 29 = vasyuninBEntry 29 39 := by
  rw [baezDuarteGramEntry_symm 39 29]
  exact G29_39_formula

theorem G39_29_interval :
    ((((20825453/645470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 29) ∧
    (baezDuarteGramEntry 39 29 ≤ (((20954547/645470000) : ℚ) : ℝ)) := by
  rw [G39_29_formula]
  exact vasyuninBEntry_29_39_eval

def interval_39_29 : NamedVasyuninInterval :=
{
  h := 39
  k := 29
  lower := (20825453/645470000)
  upper := (20954547/645470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_29_interval
}

theorem G39_30_formula : baezDuarteGramEntry 39 30 = vasyuninBEntry 30 39 := by
  rw [baezDuarteGramEntry_symm 39 30]
  exact G30_39_formula

theorem G39_30_interval :
    ((((7648523/239770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 30) ∧
    (baezDuarteGramEntry 39 30 ≤ (((7696477/239770000) : ℚ) : ℝ)) := by
  rw [G39_30_formula]
  exact vasyuninBEntry_30_39_eval

def interval_39_30 : NamedVasyuninInterval :=
{
  h := 39
  k := 30
  lower := (7648523/239770000)
  upper := (7696477/239770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_30_interval
}

theorem G39_31_formula : baezDuarteGramEntry 39 31 = vasyuninBEntry 31 39 := by
  rw [baezDuarteGramEntry_symm 39 31]
  exact G31_39_formula

theorem G39_31_interval :
    ((((6696327/211730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 31) ∧
    (baezDuarteGramEntry 39 31 ≤ (((6738673/211730000) : ℚ) : ℝ)) := by
  rw [G39_31_formula]
  exact vasyuninBEntry_31_39_eval

def interval_39_31 : NamedVasyuninInterval :=
{
  h := 39
  k := 31
  lower := (6696327/211730000)
  upper := (6738673/211730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_31_interval
}

theorem G39_32_formula : baezDuarteGramEntry 39 32 = vasyuninBEntry 32 39 := by
  rw [baezDuarteGramEntry_symm 39 32]
  exact G32_39_formula

theorem G39_32_interval :
    ((((2265281/72190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 32) ∧
    (baezDuarteGramEntry 39 32 ≤ (((2279719/72190000) : ℚ) : ℝ)) := by
  rw [G39_32_formula]
  exact vasyuninBEntry_32_39_eval

def interval_39_32 : NamedVasyuninInterval :=
{
  h := 39
  k := 32
  lower := (2265281/72190000)
  upper := (2279719/72190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_32_interval
}

theorem G39_33_formula : baezDuarteGramEntry 39 33 = vasyuninBEntry 33 39 := by
  rw [baezDuarteGramEntry_symm 39 33]
  exact G33_39_formula

theorem G39_33_interval :
    ((((27282571/874290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 33) ∧
    (baezDuarteGramEntry 39 33 ≤ (((27457429/874290000) : ℚ) : ℝ)) := by
  rw [G39_33_formula]
  exact vasyuninBEntry_33_39_eval

def interval_39_33 : NamedVasyuninInterval :=
{
  h := 39
  k := 33
  lower := (27282571/874290000)
  upper := (27457429/874290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_33_interval
}

theorem G39_34_formula : baezDuarteGramEntry 39 34 = vasyuninBEntry 34 39 := by
  rw [baezDuarteGramEntry_symm 39 34]
  exact G34_39_formula

theorem G39_34_interval :
    ((((246831/7940000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 34) ∧
    (baezDuarteGramEntry 39 34 ≤ (((248419/7940000) : ℚ) : ℝ)) := by
  rw [G39_34_formula]
  exact vasyuninBEntry_34_39_eval

def interval_39_34 : NamedVasyuninInterval :=
{
  h := 39
  k := 34
  lower := (246831/7940000)
  upper := (248419/7940000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_34_interval
}

theorem G39_35_formula : baezDuarteGramEntry 39 35 = vasyuninBEntry 35 39 := by
  rw [baezDuarteGramEntry_symm 39 35]
  exact G35_39_formula

theorem G39_35_interval :
    ((((5512239/177610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 35) ∧
    (baezDuarteGramEntry 39 35 ≤ (((5547761/177610000) : ℚ) : ℝ)) := by
  rw [G39_35_formula]
  exact vasyuninBEntry_35_39_eval

def interval_39_35 : NamedVasyuninInterval :=
{
  h := 39
  k := 35
  lower := (5512239/177610000)
  upper := (5547761/177610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_35_interval
}

theorem G39_36_formula : baezDuarteGramEntry 39 36 = vasyuninBEntry 36 39 := by
  rw [baezDuarteGramEntry_symm 39 36]
  exact G36_39_formula

theorem G39_36_interval :
    ((((1305797/42030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 36) ∧
    (baezDuarteGramEntry 39 36 ≤ (((1314203/42030000) : ℚ) : ℝ)) := by
  rw [G39_36_formula]
  exact vasyuninBEntry_36_39_eval

def interval_39_36 : NamedVasyuninInterval :=
{
  h := 39
  k := 36
  lower := (1305797/42030000)
  upper := (1314203/42030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_36_interval
}

theorem G39_37_formula : baezDuarteGramEntry 39 37 = vasyuninBEntry 37 39 := by
  rw [baezDuarteGramEntry_symm 39 37]
  exact G37_39_formula

theorem G39_37_interval :
    ((((14448693/463070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 37) ∧
    (baezDuarteGramEntry 39 37 ≤ (((14541307/463070000) : ℚ) : ℝ)) := by
  rw [G39_37_formula]
  exact vasyuninBEntry_37_39_eval

def interval_39_37 : NamedVasyuninInterval :=
{
  h := 39
  k := 37
  lower := (14448693/463070000)
  upper := (14541307/463070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_37_interval
}

theorem G39_38_formula : baezDuarteGramEntry 39 38 = vasyuninBEntry 38 39 := by
  rw [baezDuarteGramEntry_symm 39 38]
  exact G38_39_formula

theorem G39_38_interval :
    ((((6145489/195110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 38) ∧
    (baezDuarteGramEntry 39 38 ≤ (((6184511/195110000) : ℚ) : ℝ)) := by
  rw [G39_38_formula]
  exact vasyuninBEntry_38_39_eval

def interval_39_38 : NamedVasyuninInterval :=
{
  h := 39
  k := 38
  lower := (6145489/195110000)
  upper := (6184511/195110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_38_interval
}

theorem G39_39_formula_eq : baezDuarteGramEntry 39 39 = (1 / (39 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 39 := by norm_num
  rw [baez_duarte_diagonal_scaling 39 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G39_39_log_gamma_interval :
  ((((22480239/697610000) : ℚ) : ℝ) ≤ (1 / (39 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (39 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((22619761/697610000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 39 (by norm_num)
  constructor
  · have : ((((22480239/697610000) : ℚ) : ℝ) ≤ (1 / (39 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (39 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((22619761/697610000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G39_39_interval : ((((22480239/697610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 39) ∧ (baezDuarteGramEntry 39 39 ≤ (((22619761/697610000) : ℚ) : ℝ)) := by
  rw [G39_39_formula_eq]
  exact G39_39_log_gamma_interval

def interval_39_39 : NamedVasyuninInterval :=
{
  h := 39
  k := 39
  lower := (22480239/697610000)
  upper := (22619761/697610000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G39_39_interval
}

theorem G39_40_formula : baezDuarteGramEntry 39 40 = vasyuninBEntry 39 40 := vasyuninBEntry_correct_axiom 39 40

theorem vasyuninBEntry_39_40_eval :
    ((((5450257/177430000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 40) ∧
    (vasyuninBEntry 39 40 ≤ (((5485743/177430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3940_formula_bound
  constructor <;> linarith

theorem G39_40_interval :
    ((((5450257/177430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 40) ∧
    (baezDuarteGramEntry 39 40 ≤ (((5485743/177430000) : ℚ) : ℝ)) := by
  rw [G39_40_formula]
  exact vasyuninBEntry_39_40_eval

def interval_39_40 : NamedVasyuninInterval :=
{
  h := 39
  k := 40
  lower := (5450257/177430000)
  upper := (5485743/177430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_40_interval
}

theorem G39_41_formula : baezDuarteGramEntry 39 41 = vasyuninBEntry 39 41 := vasyuninBEntry_correct_axiom 39 41

theorem vasyuninBEntry_39_41_eval :
    ((((908503/30595000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 41) ∧
    (vasyuninBEntry 39 41 ≤ (((457311/15297500) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3941_formula_bound
  constructor <;> linarith

theorem G39_41_interval :
    ((((908503/30595000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 41) ∧
    (baezDuarteGramEntry 39 41 ≤ (((457311/15297500) : ℚ) : ℝ)) := by
  rw [G39_41_formula]
  exact vasyuninBEntry_39_41_eval

def interval_39_41 : NamedVasyuninInterval :=
{
  h := 39
  k := 41
  lower := (908503/30595000)
  upper := (457311/15297500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_41_interval
}

theorem G39_42_formula : baezDuarteGramEntry 39 42 = vasyuninBEntry 39 42 := vasyuninBEntry_correct_axiom 39 42

theorem vasyuninBEntry_39_42_eval :
    ((((26876869/931310000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 42) ∧
    (vasyuninBEntry 39 42 ≤ (((27063131/931310000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_14_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 14 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G39_42_interval :
    ((((26876869/931310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 42) ∧
    (baezDuarteGramEntry 39 42 ≤ (((27063131/931310000) : ℚ) : ℝ)) := by
  rw [G39_42_formula]
  exact vasyuninBEntry_39_42_eval

def interval_39_42 : NamedVasyuninInterval :=
{
  h := 39
  k := 42
  lower := (26876869/931310000)
  upper := (27063131/931310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_42_interval
}

theorem G39_43_formula : baezDuarteGramEntry 39 43 = vasyuninBEntry 39 43 := vasyuninBEntry_correct_axiom 39 43

theorem vasyuninBEntry_39_43_eval :
    ((((120721/4290000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 43) ∧
    (vasyuninBEntry 39 43 ≤ (((121579/4290000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3943_formula_bound
  constructor <;> linarith

theorem G39_43_interval :
    ((((120721/4290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 43) ∧
    (baezDuarteGramEntry 39 43 ≤ (((121579/4290000) : ℚ) : ℝ)) := by
  rw [G39_43_formula]
  exact vasyuninBEntry_39_43_eval

def interval_39_43 : NamedVasyuninInterval :=
{
  h := 39
  k := 43
  lower := (120721/4290000)
  upper := (121579/4290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_43_interval
}

theorem G39_44_formula : baezDuarteGramEntry 39 44 = vasyuninBEntry 39 44 := vasyuninBEntry_correct_axiom 39 44

theorem vasyuninBEntry_39_44_eval :
    ((((3629307/131930000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 44) ∧
    (vasyuninBEntry 39 44 ≤ (((3655693/131930000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3944_formula_bound
  constructor <;> linarith

theorem G39_44_interval :
    ((((3629307/131930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 44) ∧
    (baezDuarteGramEntry 39 44 ≤ (((3655693/131930000) : ℚ) : ℝ)) := by
  rw [G39_44_formula]
  exact vasyuninBEntry_39_44_eval

def interval_39_44 : NamedVasyuninInterval :=
{
  h := 39
  k := 44
  lower := (3629307/131930000)
  upper := (3655693/131930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_44_interval
}

theorem G39_45_formula : baezDuarteGramEntry 39 45 = vasyuninBEntry 39 45 := vasyuninBEntry_correct_axiom 39 45

theorem vasyuninBEntry_39_45_eval :
    ((((6329011/234890000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 45) ∧
    (vasyuninBEntry 39 45 ≤ (((6375989/234890000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_15_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 15 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G39_45_interval :
    ((((6329011/234890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 45) ∧
    (baezDuarteGramEntry 39 45 ≤ (((6375989/234890000) : ℚ) : ℝ)) := by
  rw [G39_45_formula]
  exact vasyuninBEntry_39_45_eval

def interval_39_45 : NamedVasyuninInterval :=
{
  h := 39
  k := 45
  lower := (6329011/234890000)
  upper := (6375989/234890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_45_interval
}

theorem G39_46_formula : baezDuarteGramEntry 39 46 = vasyuninBEntry 39 46 := vasyuninBEntry_correct_axiom 39 46

theorem vasyuninBEntry_39_46_eval :
    ((((18370497/695030000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 46) ∧
    (vasyuninBEntry 39 46 ≤ (((18509503/695030000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3946_formula_bound
  constructor <;> linarith

theorem G39_46_interval :
    ((((18370497/695030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 46) ∧
    (baezDuarteGramEntry 39 46 ≤ (((18509503/695030000) : ℚ) : ℝ)) := by
  rw [G39_46_formula]
  exact vasyuninBEntry_39_46_eval

def interval_39_46 : NamedVasyuninInterval :=
{
  h := 39
  k := 46
  lower := (18370497/695030000)
  upper := (18509503/695030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_46_interval
}

theorem G39_47_formula : baezDuarteGramEntry 39 47 = vasyuninBEntry 39 47 := vasyuninBEntry_correct_axiom 39 47

theorem vasyuninBEntry_39_47_eval :
    ((((3705731/142690000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 47) ∧
    (vasyuninBEntry 39 47 ≤ (((3734269/142690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3947_formula_bound
  constructor <;> linarith

theorem G39_47_interval :
    ((((3705731/142690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 47) ∧
    (baezDuarteGramEntry 39 47 ≤ (((3734269/142690000) : ℚ) : ℝ)) := by
  rw [G39_47_formula]
  exact vasyuninBEntry_39_47_eval

def interval_39_47 : NamedVasyuninInterval :=
{
  h := 39
  k := 47
  lower := (3705731/142690000)
  upper := (3734269/142690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_47_interval
}

theorem G39_48_formula : baezDuarteGramEntry 39 48 = vasyuninBEntry 39 48 := vasyuninBEntry_correct_axiom 39 48

theorem vasyuninBEntry_39_48_eval :
    ((((1378601/53990000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 48) ∧
    (vasyuninBEntry 39 48 ≤ (((1389399/53990000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_13_16_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 13 16 3 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 3)
  constructor <;> linarith

theorem G39_48_interval :
    ((((1378601/53990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 48) ∧
    (baezDuarteGramEntry 39 48 ≤ (((1389399/53990000) : ℚ) : ℝ)) := by
  rw [G39_48_formula]
  exact vasyuninBEntry_39_48_eval

def interval_39_48 : NamedVasyuninInterval :=
{
  h := 39
  k := 48
  lower := (1378601/53990000)
  upper := (1389399/53990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_48_interval
}

theorem G39_49_formula : baezDuarteGramEntry 39 49 = vasyuninBEntry 39 49 := vasyuninBEntry_correct_axiom 39 49

theorem vasyuninBEntry_39_49_eval :
    ((((21404881/851190000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 49) ∧
    (vasyuninBEntry 39 49 ≤ (((21575119/851190000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3949_formula_bound
  constructor <;> linarith

theorem G39_49_interval :
    ((((21404881/851190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 49) ∧
    (baezDuarteGramEntry 39 49 ≤ (((21575119/851190000) : ℚ) : ℝ)) := by
  rw [G39_49_formula]
  exact vasyuninBEntry_39_49_eval

def interval_39_49 : NamedVasyuninInterval :=
{
  h := 39
  k := 49
  lower := (21404881/851190000)
  upper := (21575119/851190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_49_interval
}

theorem G39_50_formula : baezDuarteGramEntry 39 50 = vasyuninBEntry 39 50 := vasyuninBEntry_correct_axiom 39 50

theorem vasyuninBEntry_39_50_eval :
    ((((3326563/134370000) : ℚ) : ℝ) ≤ vasyuninBEntry 39 50) ∧
    (vasyuninBEntry 39 50 ≤ (((3353437/134370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_3950_formula_bound
  constructor <;> linarith

theorem G39_50_interval :
    ((((3326563/134370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 39 50) ∧
    (baezDuarteGramEntry 39 50 ≤ (((3353437/134370000) : ℚ) : ℝ)) := by
  rw [G39_50_formula]
  exact vasyuninBEntry_39_50_eval

def interval_39_50 : NamedVasyuninInterval :=
{
  h := 39
  k := 50
  lower := (3326563/134370000)
  upper := (3353437/134370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G39_50_interval
}

theorem G40_1_formula : baezDuarteGramEntry 40 1 = vasyuninBEntry 1 40 := by
  rw [baezDuarteGramEntry_symm 40 1]
  exact G1_40_formula

theorem G40_1_interval :
    ((((7366343/99070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 1) ∧
    (baezDuarteGramEntry 40 1 ≤ (((7386157/99070000) : ℚ) : ℝ)) := by
  rw [G40_1_formula]
  exact vasyuninBEntry_1_40_eval

def interval_40_1 : NamedVasyuninInterval :=
{
  h := 40
  k := 1
  lower := (7366343/99070000)
  upper := (7386157/99070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_1_interval
}

theorem G40_2_formula : baezDuarteGramEntry 40 2 = vasyuninBEntry 2 40 := by
  rw [baezDuarteGramEntry_symm 40 2]
  exact G2_40_formula

theorem G40_2_interval :
    ((((59749163/908370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 2) ∧
    (baezDuarteGramEntry 40 2 ≤ (((59930837/908370000) : ℚ) : ℝ)) := by
  rw [G40_2_formula]
  exact vasyuninBEntry_2_40_eval

def interval_40_2 : NamedVasyuninInterval :=
{
  h := 40
  k := 2
  lower := (59749163/908370000)
  upper := (59930837/908370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_2_interval
}

theorem G40_3_formula : baezDuarteGramEntry 40 3 = vasyuninBEntry 3 40 := by
  rw [baezDuarteGramEntry_symm 40 3]
  exact G3_40_formula

theorem G40_3_interval :
    ((((170281/2815000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 3) ∧
    (baezDuarteGramEntry 40 3 ≤ (((42711/703750) : ℚ) : ℝ)) := by
  rw [G40_3_formula]
  exact vasyuninBEntry_3_40_eval

def interval_40_3 : NamedVasyuninInterval :=
{
  h := 40
  k := 3
  lower := (170281/2815000)
  upper := (42711/703750)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_3_interval
}

theorem G40_4_formula : baezDuarteGramEntry 40 4 = vasyuninBEntry 4 40 := by
  rw [baezDuarteGramEntry_symm 40 4]
  exact G4_40_formula

theorem G40_4_interval :
    ((((20339493/355070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 4) ∧
    (baezDuarteGramEntry 40 4 ≤ (((20410507/355070000) : ℚ) : ℝ)) := by
  rw [G40_4_formula]
  exact vasyuninBEntry_4_40_eval

def interval_40_4 : NamedVasyuninInterval :=
{
  h := 40
  k := 4
  lower := (20339493/355070000)
  upper := (20410507/355070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_4_interval
}

theorem G40_5_formula : baezDuarteGramEntry 40 5 = vasyuninBEntry 5 40 := by
  rw [baezDuarteGramEntry_symm 40 5]
  exact G5_40_formula

theorem G40_5_interval :
    ((((42731707/782930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 5) ∧
    (baezDuarteGramEntry 40 5 ≤ (((42888293/782930000) : ℚ) : ℝ)) := by
  rw [G40_5_formula]
  exact vasyuninBEntry_5_40_eval

def interval_40_5 : NamedVasyuninInterval :=
{
  h := 40
  k := 5
  lower := (42731707/782930000)
  upper := (42888293/782930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_5_interval
}

theorem G40_6_formula : baezDuarteGramEntry 40 6 = vasyuninBEntry 6 40 := by
  rw [baezDuarteGramEntry_symm 40 6]
  exact G6_40_formula

theorem G40_6_interval :
    ((((18798689/363110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 6) ∧
    (baezDuarteGramEntry 40 6 ≤ (((18871311/363110000) : ℚ) : ℝ)) := by
  rw [G40_6_formula]
  exact vasyuninBEntry_6_40_eval

def interval_40_6 : NamedVasyuninInterval :=
{
  h := 40
  k := 6
  lower := (18798689/363110000)
  upper := (18871311/363110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_6_interval
}

theorem G40_7_formula : baezDuarteGramEntry 40 7 = vasyuninBEntry 7 40 := by
  rw [baezDuarteGramEntry_symm 40 7]
  exact G7_40_formula

theorem G40_7_interval :
    ((((47015637/943630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 7) ∧
    (baezDuarteGramEntry 40 7 ≤ (((47204363/943630000) : ℚ) : ℝ)) := by
  rw [G40_7_formula]
  exact vasyuninBEntry_7_40_eval

def interval_40_7 : NamedVasyuninInterval :=
{
  h := 40
  k := 7
  lower := (47015637/943630000)
  upper := (47204363/943630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_7_interval
}

theorem G40_8_formula : baezDuarteGramEntry 40 8 = vasyuninBEntry 8 40 := by
  rw [baezDuarteGramEntry_symm 40 8]
  exact G8_40_formula

theorem G40_8_interval :
    ((((26116657/533430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 8) ∧
    (baezDuarteGramEntry 40 8 ≤ (((26223343/533430000) : ℚ) : ℝ)) := by
  rw [G40_8_formula]
  exact vasyuninBEntry_8_40_eval

def interval_40_8 : NamedVasyuninInterval :=
{
  h := 40
  k := 8
  lower := (26116657/533430000)
  upper := (26223343/533430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_8_interval
}

theorem G40_9_formula : baezDuarteGramEntry 40 9 = vasyuninBEntry 9 40 := by
  rw [baezDuarteGramEntry_symm 40 9]
  exact G9_40_formula

theorem G40_9_interval :
    ((((2338109/50160000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 9) ∧
    (baezDuarteGramEntry 40 9 ≤ (((2348141/50160000) : ℚ) : ℝ)) := by
  rw [G40_9_formula]
  exact vasyuninBEntry_9_40_eval

def interval_40_9 : NamedVasyuninInterval :=
{
  h := 40
  k := 9
  lower := (2338109/50160000)
  upper := (2348141/50160000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_9_interval
}

theorem G40_10_formula : baezDuarteGramEntry 40 10 = vasyuninBEntry 10 40 := by
  rw [baezDuarteGramEntry_symm 40 10]
  exact G10_40_formula

theorem G40_10_interval :
    ((((10908959/235410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 10) ∧
    (baezDuarteGramEntry 40 10 ≤ (((10956041/235410000) : ℚ) : ℝ)) := by
  rw [G40_10_formula]
  exact vasyuninBEntry_10_40_eval

def interval_40_10 : NamedVasyuninInterval :=
{
  h := 40
  k := 10
  lower := (10908959/235410000)
  upper := (10956041/235410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_10_interval
}

theorem G40_11_formula : baezDuarteGramEntry 40 11 = vasyuninBEntry 11 40 := by
  rw [baezDuarteGramEntry_symm 40 11]
  exact G11_40_formula

theorem G40_11_interval :
    ((((295569/6710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 11) ∧
    (baezDuarteGramEntry 40 11 ≤ (((296911/6710000) : ℚ) : ℝ)) := by
  rw [G40_11_formula]
  exact vasyuninBEntry_11_40_eval

def interval_40_11 : NamedVasyuninInterval :=
{
  h := 40
  k := 11
  lower := (295569/6710000)
  upper := (296911/6710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_11_interval
}

theorem G40_12_formula : baezDuarteGramEntry 40 12 = vasyuninBEntry 12 40 := by
  rw [baezDuarteGramEntry_symm 40 12]
  exact G12_40_formula

theorem G40_12_interval :
    ((((37014009/859910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 12) ∧
    (baezDuarteGramEntry 40 12 ≤ (((37185991/859910000) : ℚ) : ℝ)) := by
  rw [G40_12_formula]
  exact vasyuninBEntry_12_40_eval

def interval_40_12 : NamedVasyuninInterval :=
{
  h := 40
  k := 12
  lower := (37014009/859910000)
  upper := (37185991/859910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_12_interval
}

theorem G40_13_formula : baezDuarteGramEntry 40 13 = vasyuninBEntry 13 40 := by
  rw [baezDuarteGramEntry_symm 40 13]
  exact G13_40_formula

theorem G40_13_interval :
    ((((6708259/157410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 13) ∧
    (baezDuarteGramEntry 40 13 ≤ (((6739741/157410000) : ℚ) : ℝ)) := by
  rw [G40_13_formula]
  exact vasyuninBEntry_13_40_eval

def interval_40_13 : NamedVasyuninInterval :=
{
  h := 40
  k := 13
  lower := (6708259/157410000)
  upper := (6739741/157410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_13_interval
}

theorem G40_14_formula : baezDuarteGramEntry 40 14 = vasyuninBEntry 14 40 := by
  rw [baezDuarteGramEntry_symm 40 14]
  exact G14_40_formula

theorem G40_14_interval :
    ((((38975703/942970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 14) ∧
    (baezDuarteGramEntry 40 14 ≤ (((39164297/942970000) : ℚ) : ℝ)) := by
  rw [G40_14_formula]
  exact vasyuninBEntry_14_40_eval

def interval_40_14 : NamedVasyuninInterval :=
{
  h := 40
  k := 14
  lower := (38975703/942970000)
  upper := (39164297/942970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_14_interval
}

theorem G40_15_formula : baezDuarteGramEntry 40 15 = vasyuninBEntry 15 40 := by
  rw [baezDuarteGramEntry_symm 40 15]
  exact G15_40_formula

theorem G40_15_interval :
    ((((30863129/768710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 15) ∧
    (baezDuarteGramEntry 40 15 ≤ (((31016871/768710000) : ℚ) : ℝ)) := by
  rw [G40_15_formula]
  exact vasyuninBEntry_15_40_eval

def interval_40_15 : NamedVasyuninInterval :=
{
  h := 40
  k := 15
  lower := (30863129/768710000)
  upper := (31016871/768710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_15_interval
}

theorem G40_16_formula : baezDuarteGramEntry 40 16 = vasyuninBEntry 16 40 := by
  rw [baezDuarteGramEntry_symm 40 16]
  exact G16_40_formula

theorem G40_16_interval :
    ((((4552211/115390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 16) ∧
    (baezDuarteGramEntry 40 16 ≤ (((4575289/115390000) : ℚ) : ℝ)) := by
  rw [G40_16_formula]
  exact vasyuninBEntry_16_40_eval

def interval_40_16 : NamedVasyuninInterval :=
{
  h := 40
  k := 16
  lower := (4552211/115390000)
  upper := (4575289/115390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_16_interval
}

theorem G40_17_formula : baezDuarteGramEntry 40 17 = vasyuninBEntry 17 40 := by
  rw [baezDuarteGramEntry_symm 40 17]
  exact G17_40_formula

theorem G40_17_interval :
    ((((28127059/729410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 17) ∧
    (baezDuarteGramEntry 40 17 ≤ (((28272941/729410000) : ℚ) : ℝ)) := by
  rw [G40_17_formula]
  exact vasyuninBEntry_17_40_eval

def interval_40_17 : NamedVasyuninInterval :=
{
  h := 40
  k := 17
  lower := (28127059/729410000)
  upper := (28272941/729410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_17_interval
}

theorem G40_18_formula : baezDuarteGramEntry 40 18 = vasyuninBEntry 18 40 := by
  rw [baezDuarteGramEntry_symm 40 18]
  exact G18_40_formula

theorem G40_18_interval :
    ((((3453427/90730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 18) ∧
    (baezDuarteGramEntry 40 18 ≤ (((3471573/90730000) : ℚ) : ℝ)) := by
  rw [G40_18_formula]
  exact vasyuninBEntry_18_40_eval

def interval_40_18 : NamedVasyuninInterval :=
{
  h := 40
  k := 18
  lower := (3453427/90730000)
  upper := (3471573/90730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_18_interval
}

theorem G40_19_formula : baezDuarteGramEntry 40 19 = vasyuninBEntry 19 40 := by
  rw [baezDuarteGramEntry_symm 40 19]
  exact G19_40_formula

theorem G40_19_interval :
    ((((25602411/675890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 19) ∧
    (baezDuarteGramEntry 40 19 ≤ (((25737589/675890000) : ℚ) : ℝ)) := by
  rw [G40_19_formula]
  exact vasyuninBEntry_19_40_eval

def interval_40_19 : NamedVasyuninInterval :=
{
  h := 40
  k := 19
  lower := (25602411/675890000)
  upper := (25737589/675890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_19_interval
}

theorem G40_20_formula : baezDuarteGramEntry 40 20 = vasyuninBEntry 20 40 := by
  rw [baezDuarteGramEntry_symm 40 20]
  exact G20_40_formula

theorem G40_20_interval :
    ((((2804717/72830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 20) ∧
    (baezDuarteGramEntry 40 20 ≤ (((2819283/72830000) : ℚ) : ℝ)) := by
  rw [G40_20_formula]
  exact vasyuninBEntry_20_40_eval

def interval_40_20 : NamedVasyuninInterval :=
{
  h := 40
  k := 20
  lower := (2804717/72830000)
  upper := (2819283/72830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_20_interval
}

theorem G40_21_formula : baezDuarteGramEntry 40 21 = vasyuninBEntry 21 40 := by
  rw [baezDuarteGramEntry_symm 40 21]
  exact G21_40_formula

theorem G40_21_interval :
    ((((441293/12070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 21) ∧
    (baezDuarteGramEntry 40 21 ≤ (((443707/12070000) : ℚ) : ℝ)) := by
  rw [G40_21_formula]
  exact vasyuninBEntry_21_40_eval

def interval_40_21 : NamedVasyuninInterval :=
{
  h := 40
  k := 21
  lower := (441293/12070000)
  upper := (443707/12070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_21_interval
}

theorem G40_22_formula : baezDuarteGramEntry 40 22 = vasyuninBEntry 22 40 := by
  rw [baezDuarteGramEntry_symm 40 22]
  exact G22_40_formula

theorem G40_22_interval :
    ((((19225797/542030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 22) ∧
    (baezDuarteGramEntry 40 22 ≤ (((19334203/542030000) : ℚ) : ℝ)) := by
  rw [G40_22_formula]
  exact vasyuninBEntry_22_40_eval

def interval_40_22 : NamedVasyuninInterval :=
{
  h := 40
  k := 22
  lower := (19225797/542030000)
  upper := (19334203/542030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_22_interval
}

theorem G40_23_formula : baezDuarteGramEntry 40 23 = vasyuninBEntry 23 40 := by
  rw [baezDuarteGramEntry_symm 40 23]
  exact G23_40_formula

theorem G40_23_interval :
    ((((161883/4670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 23) ∧
    (baezDuarteGramEntry 40 23 ≤ (((162817/4670000) : ℚ) : ℝ)) := by
  rw [G40_23_formula]
  exact vasyuninBEntry_23_40_eval

def interval_40_23 : NamedVasyuninInterval :=
{
  h := 40
  k := 23
  lower := (161883/4670000)
  upper := (162817/4670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_23_interval
}

theorem G40_24_formula : baezDuarteGramEntry 40 24 = vasyuninBEntry 24 40 := by
  rw [baezDuarteGramEntry_symm 40 24]
  exact G24_40_formula

theorem G40_24_interval :
    ((((10055507/294930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 24) ∧
    (baezDuarteGramEntry 40 24 ≤ (((10114493/294930000) : ℚ) : ℝ)) := by
  rw [G40_24_formula]
  exact vasyuninBEntry_24_40_eval

def interval_40_24 : NamedVasyuninInterval :=
{
  h := 40
  k := 24
  lower := (10055507/294930000)
  upper := (10114493/294930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_24_interval
}

theorem G40_25_formula : baezDuarteGramEntry 40 25 = vasyuninBEntry 25 40 := by
  rw [baezDuarteGramEntry_symm 40 25]
  exact G25_40_formula

theorem G40_25_interval :
    ((((12223471/365290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 25) ∧
    (baezDuarteGramEntry 40 25 ≤ (((12296529/365290000) : ℚ) : ℝ)) := by
  rw [G40_25_formula]
  exact vasyuninBEntry_25_40_eval

def interval_40_25 : NamedVasyuninInterval :=
{
  h := 40
  k := 25
  lower := (12223471/365290000)
  upper := (12296529/365290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_25_interval
}

theorem G40_26_formula : baezDuarteGramEntry 40 26 = vasyuninBEntry 26 40 := by
  rw [baezDuarteGramEntry_symm 40 26]
  exact G26_40_formula

theorem G40_26_interval :
    ((((1324739/40110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 26) ∧
    (baezDuarteGramEntry 40 26 ≤ (((1332761/40110000) : ℚ) : ℝ)) := by
  rw [G40_26_formula]
  exact vasyuninBEntry_26_40_eval

def interval_40_26 : NamedVasyuninInterval :=
{
  h := 40
  k := 26
  lower := (1324739/40110000)
  upper := (1332761/40110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_26_interval
}

theorem G40_27_formula : baezDuarteGramEntry 40 27 = vasyuninBEntry 27 40 := by
  rw [baezDuarteGramEntry_symm 40 27]
  exact G27_40_formula

theorem G40_27_interval :
    ((((27505753/842470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 27) ∧
    (baezDuarteGramEntry 40 27 ≤ (((27674247/842470000) : ℚ) : ℝ)) := by
  rw [G40_27_formula]
  exact vasyuninBEntry_27_40_eval

def interval_40_27 : NamedVasyuninInterval :=
{
  h := 40
  k := 27
  lower := (27505753/842470000)
  upper := (27674247/842470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_27_interval
}

theorem G40_28_formula : baezDuarteGramEntry 40 28 = vasyuninBEntry 28 40 := by
  rw [baezDuarteGramEntry_symm 40 28]
  exact G28_40_formula

theorem G40_28_interval :
    ((((3686509/114910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 28) ∧
    (baezDuarteGramEntry 40 28 ≤ (((3709491/114910000) : ℚ) : ℝ)) := by
  rw [G40_28_formula]
  exact vasyuninBEntry_28_40_eval

def interval_40_28 : NamedVasyuninInterval :=
{
  h := 40
  k := 28
  lower := (3686509/114910000)
  upper := (3709491/114910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_28_interval
}

theorem G40_29_formula : baezDuarteGramEntry 40 29 = vasyuninBEntry 29 40 := by
  rw [baezDuarteGramEntry_symm 40 29]
  exact G29_40_formula

theorem G40_29_interval :
    ((((28669469/905310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 29) ∧
    (baezDuarteGramEntry 40 29 ≤ (((28850531/905310000) : ℚ) : ℝ)) := by
  rw [G40_29_formula]
  exact vasyuninBEntry_29_40_eval

def interval_40_29 : NamedVasyuninInterval :=
{
  h := 40
  k := 29
  lower := (28669469/905310000)
  upper := (28850531/905310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_29_interval
}

theorem G40_30_formula : baezDuarteGramEntry 40 30 = vasyuninBEntry 30 40 := by
  rw [baezDuarteGramEntry_symm 40 30]
  exact G30_40_formula

theorem G40_30_interval :
    ((((1259993/40070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 30) ∧
    (baezDuarteGramEntry 40 30 ≤ (((1268007/40070000) : ℚ) : ℝ)) := by
  rw [G40_30_formula]
  exact vasyuninBEntry_30_40_eval

def interval_40_30 : NamedVasyuninInterval :=
{
  h := 40
  k := 30
  lower := (1259993/40070000)
  upper := (1268007/40070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_30_interval
}

theorem G40_31_formula : baezDuarteGramEntry 40 31 = vasyuninBEntry 31 40 := by
  rw [baezDuarteGramEntry_symm 40 31]
  exact G31_40_formula

theorem G40_31_interval :
    ((((28258921/910790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 31) ∧
    (baezDuarteGramEntry 40 31 ≤ (((28441079/910790000) : ℚ) : ℝ)) := by
  rw [G40_31_formula]
  exact vasyuninBEntry_31_40_eval

def interval_40_31 : NamedVasyuninInterval :=
{
  h := 40
  k := 31
  lower := (28258921/910790000)
  upper := (28441079/910790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_31_interval
}

theorem G40_32_formula : baezDuarteGramEntry 40 32 = vasyuninBEntry 32 40 := by
  rw [baezDuarteGramEntry_symm 40 32]
  exact G32_40_formula

theorem G40_32_interval :
    ((((14652461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 32) ∧
    (baezDuarteGramEntry 40 32 ≤ (((14747539/475390000) : ℚ) : ℝ)) := by
  rw [G40_32_formula]
  exact vasyuninBEntry_32_40_eval

def interval_40_32 : NamedVasyuninInterval :=
{
  h := 40
  k := 32
  lower := (14652461/475390000)
  upper := (14747539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_32_interval
}

theorem G40_33_formula : baezDuarteGramEntry 40 33 = vasyuninBEntry 33 40 := by
  rw [baezDuarteGramEntry_symm 40 33]
  exact G33_40_formula

theorem G40_33_interval :
    ((((11178421/365790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 33) ∧
    (baezDuarteGramEntry 40 33 ≤ (((11251579/365790000) : ℚ) : ℝ)) := by
  rw [G40_33_formula]
  exact vasyuninBEntry_33_40_eval

def interval_40_33 : NamedVasyuninInterval :=
{
  h := 40
  k := 33
  lower := (11178421/365790000)
  upper := (11251579/365790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_33_interval
}

theorem G40_34_formula : baezDuarteGramEntry 40 34 = vasyuninBEntry 34 40 := by
  rw [baezDuarteGramEntry_symm 40 34]
  exact G34_40_formula

theorem G40_34_interval :
    ((((21499279/707210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 34) ∧
    (baezDuarteGramEntry 40 34 ≤ (((21640721/707210000) : ℚ) : ℝ)) := by
  rw [G40_34_formula]
  exact vasyuninBEntry_34_40_eval

def interval_40_34 : NamedVasyuninInterval :=
{
  h := 40
  k := 34
  lower := (21499279/707210000)
  upper := (21640721/707210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_34_interval
}

theorem G40_35_formula : baezDuarteGramEntry 40 35 = vasyuninBEntry 35 40 := by
  rw [baezDuarteGramEntry_symm 40 35]
  exact G35_40_formula

theorem G40_35_interval :
    ((((2630321/86790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 35) ∧
    (baezDuarteGramEntry 40 35 ≤ (((2647679/86790000) : ℚ) : ℝ)) := by
  rw [G40_35_formula]
  exact vasyuninBEntry_35_40_eval

def interval_40_35 : NamedVasyuninInterval :=
{
  h := 40
  k := 35
  lower := (2630321/86790000)
  upper := (2647679/86790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_35_interval
}

theorem G40_36_formula : baezDuarteGramEntry 40 36 = vasyuninBEntry 36 40 := by
  rw [baezDuarteGramEntry_symm 40 36]
  exact G36_40_formula

theorem G40_36_interval :
    ((((1723679/56960000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 36) ∧
    (baezDuarteGramEntry 40 36 ≤ (((1735071/56960000) : ℚ) : ℝ)) := by
  rw [G40_36_formula]
  exact vasyuninBEntry_36_40_eval

def interval_40_36 : NamedVasyuninInterval :=
{
  h := 40
  k := 36
  lower := (1723679/56960000)
  upper := (1735071/56960000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_36_interval
}

theorem G40_37_formula : baezDuarteGramEntry 40 37 = vasyuninBEntry 37 40 := by
  rw [baezDuarteGramEntry_symm 40 37]
  exact G37_40_formula

theorem G40_37_interval :
    ((((17990611/593890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 37) ∧
    (baezDuarteGramEntry 40 37 ≤ (((18109389/593890000) : ℚ) : ℝ)) := by
  rw [G40_37_formula]
  exact vasyuninBEntry_37_40_eval

def interval_40_37 : NamedVasyuninInterval :=
{
  h := 40
  k := 37
  lower := (17990611/593890000)
  upper := (18109389/593890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_37_interval
}

theorem G40_38_formula : baezDuarteGramEntry 40 38 = vasyuninBEntry 38 40 := by
  rw [baezDuarteGramEntry_symm 40 38]
  exact G38_40_formula

theorem G40_38_interval :
    ((((27140809/891910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 38) ∧
    (baezDuarteGramEntry 40 38 ≤ (((27319191/891910000) : ℚ) : ℝ)) := by
  rw [G40_38_formula]
  exact vasyuninBEntry_38_40_eval

def interval_40_38 : NamedVasyuninInterval :=
{
  h := 40
  k := 38
  lower := (27140809/891910000)
  upper := (27319191/891910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_38_interval
}

theorem G40_39_formula : baezDuarteGramEntry 40 39 = vasyuninBEntry 39 40 := by
  rw [baezDuarteGramEntry_symm 40 39]
  exact G39_40_formula

theorem G40_39_interval :
    ((((5450257/177430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 39) ∧
    (baezDuarteGramEntry 40 39 ≤ (((5485743/177430000) : ℚ) : ℝ)) := by
  rw [G40_39_formula]
  exact vasyuninBEntry_39_40_eval

def interval_40_39 : NamedVasyuninInterval :=
{
  h := 40
  k := 39
  lower := (5450257/177430000)
  upper := (5485743/177430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_39_interval
}

theorem G40_40_formula_eq : baezDuarteGramEntry 40 40 = (1 / (40 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 40 := by norm_num
  rw [baez_duarte_diagonal_scaling 40 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G40_40_log_gamma_interval :
  ((((9908461/315390000) : ℚ) : ℝ) ≤ (1 / (40 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (40 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((9971539/315390000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 40 (by norm_num)
  constructor
  · have : ((((9908461/315390000) : ℚ) : ℝ) ≤ (1 / (40 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (40 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((9971539/315390000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G40_40_interval : ((((9908461/315390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 40) ∧ (baezDuarteGramEntry 40 40 ≤ (((9971539/315390000) : ℚ) : ℝ)) := by
  rw [G40_40_formula_eq]
  exact G40_40_log_gamma_interval

def interval_40_40 : NamedVasyuninInterval :=
{
  h := 40
  k := 40
  lower := (9908461/315390000)
  upper := (9971539/315390000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G40_40_interval
}

theorem G40_41_formula : baezDuarteGramEntry 40 41 = vasyuninBEntry 40 41 := vasyuninBEntry_correct_axiom 40 41

theorem vasyuninBEntry_40_41_eval :
    ((((24418539/814610000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 41) ∧
    (vasyuninBEntry 40 41 ≤ (((24581461/814610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4041_formula_bound
  constructor <;> linarith

theorem G40_41_interval :
    ((((24418539/814610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 41) ∧
    (baezDuarteGramEntry 40 41 ≤ (((24581461/814610000) : ℚ) : ℝ)) := by
  rw [G40_41_formula]
  exact vasyuninBEntry_40_41_eval

def interval_40_41 : NamedVasyuninInterval :=
{
  h := 40
  k := 41
  lower := (24418539/814610000)
  upper := (24581461/814610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_41_interval
}

theorem G40_42_formula : baezDuarteGramEntry 40 42 = vasyuninBEntry 40 42 := vasyuninBEntry_correct_axiom 40 42

theorem vasyuninBEntry_40_42_eval :
    ((((16817/580000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 42) ∧
    (vasyuninBEntry 40 42 ≤ (((16933/580000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_20_21_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 20 21 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G40_42_interval :
    ((((16817/580000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 42) ∧
    (baezDuarteGramEntry 40 42 ≤ (((16933/580000) : ℚ) : ℝ)) := by
  rw [G40_42_formula]
  exact vasyuninBEntry_40_42_eval

def interval_40_42 : NamedVasyuninInterval :=
{
  h := 40
  k := 42
  lower := (16817/580000)
  upper := (16933/580000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_42_interval
}

theorem G40_43_formula : baezDuarteGramEntry 40 43 = vasyuninBEntry 40 43 := vasyuninBEntry_correct_axiom 40 43

theorem vasyuninBEntry_40_43_eval :
    ((((229187/8130000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 43) ∧
    (vasyuninBEntry 40 43 ≤ (((230813/8130000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4043_formula_bound
  constructor <;> linarith

theorem G40_43_interval :
    ((((229187/8130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 43) ∧
    (baezDuarteGramEntry 40 43 ≤ (((230813/8130000) : ℚ) : ℝ)) := by
  rw [G40_43_formula]
  exact vasyuninBEntry_40_43_eval

def interval_40_43 : NamedVasyuninInterval :=
{
  h := 40
  k := 43
  lower := (229187/8130000)
  upper := (230813/8130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_43_interval
}

theorem G40_44_formula : baezDuarteGramEntry 40 44 = vasyuninBEntry 40 44 := vasyuninBEntry_correct_axiom 40 44

theorem vasyuninBEntry_40_44_eval :
    ((((13077451/475490000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 44) ∧
    (vasyuninBEntry 40 44 ≤ (((13172549/475490000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_10_11_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 10 11 4 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 4)
  constructor <;> linarith

theorem G40_44_interval :
    ((((13077451/475490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 44) ∧
    (baezDuarteGramEntry 40 44 ≤ (((13172549/475490000) : ℚ) : ℝ)) := by
  rw [G40_44_formula]
  exact vasyuninBEntry_40_44_eval

def interval_40_44 : NamedVasyuninInterval :=
{
  h := 40
  k := 44
  lower := (13077451/475490000)
  upper := (13172549/475490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_44_interval
}

theorem G40_45_formula : baezDuarteGramEntry 40 45 = vasyuninBEntry 40 45 := vasyuninBEntry_correct_axiom 40 45

theorem vasyuninBEntry_40_45_eval :
    ((((14685403/545970000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 45) ∧
    (vasyuninBEntry 40 45 ≤ (((14794597/545970000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_8_9_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 8 9 5 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 5)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 5)
  constructor <;> linarith

theorem G40_45_interval :
    ((((14685403/545970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 45) ∧
    (baezDuarteGramEntry 40 45 ≤ (((14794597/545970000) : ℚ) : ℝ)) := by
  rw [G40_45_formula]
  exact vasyuninBEntry_40_45_eval

def interval_40_45 : NamedVasyuninInterval :=
{
  h := 40
  k := 45
  lower := (14685403/545970000)
  upper := (14794597/545970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_45_interval
}

theorem G40_46_formula : baezDuarteGramEntry 40 46 = vasyuninBEntry 40 46 := vasyuninBEntry_correct_axiom 40 46

theorem vasyuninBEntry_40_46_eval :
    ((((39553/1501250) : ℚ) : ℝ) ≤ vasyuninBEntry 40 46) ∧
    (vasyuninBEntry 40 46 ≤ (((159413/6005000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_20_23_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 20 23 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G40_46_interval :
    ((((39553/1501250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 46) ∧
    (baezDuarteGramEntry 40 46 ≤ (((159413/6005000) : ℚ) : ℝ)) := by
  rw [G40_46_formula]
  exact vasyuninBEntry_40_46_eval

def interval_40_46 : NamedVasyuninInterval :=
{
  h := 40
  k := 46
  lower := (39553/1501250)
  upper := (159413/6005000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_46_interval
}

theorem G40_47_formula : baezDuarteGramEntry 40 47 = vasyuninBEntry 40 47 := vasyuninBEntry_correct_axiom 40 47

theorem vasyuninBEntry_40_47_eval :
    ((((196739/7610000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 47) ∧
    (vasyuninBEntry 40 47 ≤ (((198261/7610000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4047_formula_bound
  constructor <;> linarith

theorem G40_47_interval :
    ((((196739/7610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 47) ∧
    (baezDuarteGramEntry 40 47 ≤ (((198261/7610000) : ℚ) : ℝ)) := by
  rw [G40_47_formula]
  exact vasyuninBEntry_40_47_eval

def interval_40_47 : NamedVasyuninInterval :=
{
  h := 40
  k := 47
  lower := (196739/7610000)
  upper := (198261/7610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_47_interval
}

theorem G40_48_formula : baezDuarteGramEntry 40 48 = vasyuninBEntry 40 48 := vasyuninBEntry_correct_axiom 40 48

theorem vasyuninBEntry_40_48_eval :
    ((((4357859/171410000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 48) ∧
    (vasyuninBEntry 40 48 ≤ (((4392141/171410000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_5_6_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 5 6 8 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 8)
  constructor <;> linarith

theorem G40_48_interval :
    ((((4357859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 48) ∧
    (baezDuarteGramEntry 40 48 ≤ (((4392141/171410000) : ℚ) : ℝ)) := by
  rw [G40_48_formula]
  exact vasyuninBEntry_40_48_eval

def interval_40_48 : NamedVasyuninInterval :=
{
  h := 40
  k := 48
  lower := (4357859/171410000)
  upper := (4392141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_48_interval
}

theorem G40_49_formula : baezDuarteGramEntry 40 49 = vasyuninBEntry 40 49 := vasyuninBEntry_correct_axiom 40 49

theorem vasyuninBEntry_40_49_eval :
    ((((6254963/250370000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 49) ∧
    (vasyuninBEntry 40 49 ≤ (((6305037/250370000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4049_formula_bound
  constructor <;> linarith

theorem G40_49_interval :
    ((((6254963/250370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 49) ∧
    (baezDuarteGramEntry 40 49 ≤ (((6305037/250370000) : ℚ) : ℝ)) := by
  rw [G40_49_formula]
  exact vasyuninBEntry_40_49_eval

def interval_40_49 : NamedVasyuninInterval :=
{
  h := 40
  k := 49
  lower := (6254963/250370000)
  upper := (6305037/250370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_49_interval
}

theorem G40_50_formula : baezDuarteGramEntry 40 50 = vasyuninBEntry 40 50 := vasyuninBEntry_correct_axiom 40 50

theorem vasyuninBEntry_40_50_eval :
    ((((11712461/475390000) : ℚ) : ℝ) ≤ vasyuninBEntry 40 50) ∧
    (vasyuninBEntry 40 50 ≤ (((11807539/475390000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_4_5_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 4 5 10 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 10)
  constructor <;> linarith

theorem G40_50_interval :
    ((((11712461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 40 50) ∧
    (baezDuarteGramEntry 40 50 ≤ (((11807539/475390000) : ℚ) : ℝ)) := by
  rw [G40_50_formula]
  exact vasyuninBEntry_40_50_eval

def interval_40_50 : NamedVasyuninInterval :=
{
  h := 40
  k := 50
  lower := (11712461/475390000)
  upper := (11807539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G40_50_interval
}

theorem G41_1_formula : baezDuarteGramEntry 41 1 = vasyuninBEntry 1 41 := by
  rw [baezDuarteGramEntry_symm 41 1]
  exact G1_41_formula

theorem G41_1_interval :
    ((((56422537/774630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 1) ∧
    (baezDuarteGramEntry 41 1 ≤ (((56577463/774630000) : ℚ) : ℝ)) := by
  rw [G41_1_formula]
  exact vasyuninBEntry_1_41_eval

def interval_41_1 : NamedVasyuninInterval :=
{
  h := 41
  k := 1
  lower := (56422537/774630000)
  upper := (56577463/774630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_1_interval
}

theorem G41_2_formula : baezDuarteGramEntry 41 2 = vasyuninBEntry 2 41 := by
  rw [baezDuarteGramEntry_symm 41 2]
  exact G2_41_formula

theorem G41_2_interval :
    ((((62362987/970130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 2) ∧
    (baezDuarteGramEntry 41 2 ≤ (((62557013/970130000) : ℚ) : ℝ)) := by
  rw [G41_2_formula]
  exact vasyuninBEntry_2_41_eval

def interval_41_2 : NamedVasyuninInterval :=
{
  h := 41
  k := 2
  lower := (62362987/970130000)
  upper := (62557013/970130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_2_interval
}

theorem G41_3_formula : baezDuarteGramEntry 41 3 = vasyuninBEntry 3 41 := by
  rw [baezDuarteGramEntry_symm 41 3]
  exact G3_41_formula

theorem G41_3_interval :
    ((((47599747/802530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 3) ∧
    (baezDuarteGramEntry 41 3 ≤ (((47760253/802530000) : ℚ) : ℝ)) := by
  rw [G41_3_formula]
  exact vasyuninBEntry_3_41_eval

def interval_41_3 : NamedVasyuninInterval :=
{
  h := 41
  k := 3
  lower := (47599747/802530000)
  upper := (47760253/802530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_3_interval
}

theorem G41_4_formula : baezDuarteGramEntry 41 4 = vasyuninBEntry 4 41 := by
  rw [baezDuarteGramEntry_symm 41 4]
  exact G4_41_formula

theorem G41_4_interval :
    ((((17598469/315310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 4) ∧
    (baezDuarteGramEntry 41 4 ≤ (((17661531/315310000) : ℚ) : ℝ)) := by
  rw [G41_4_formula]
  exact vasyuninBEntry_4_41_eval

def interval_41_4 : NamedVasyuninInterval :=
{
  h := 41
  k := 4
  lower := (17598469/315310000)
  upper := (17661531/315310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_4_interval
}

theorem G41_5_formula : baezDuarteGramEntry 41 5 = vasyuninBEntry 5 41 := by
  rw [baezDuarteGramEntry_symm 41 5]
  exact G5_41_formula

theorem G41_5_interval :
    ((((15520779/292210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 5) ∧
    (baezDuarteGramEntry 41 5 ≤ (((15579221/292210000) : ℚ) : ℝ)) := by
  rw [G41_5_formula]
  exact vasyuninBEntry_5_41_eval

def interval_41_5 : NamedVasyuninInterval :=
{
  h := 41
  k := 5
  lower := (15520779/292210000)
  upper := (15579221/292210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_5_interval
}

theorem G41_6_formula : baezDuarteGramEntry 41 6 = vasyuninBEntry 6 41 := by
  rw [baezDuarteGramEntry_symm 41 6]
  exact G6_41_formula

theorem G41_6_interval :
    ((((5844769/114810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 6) ∧
    (baezDuarteGramEntry 41 6 ≤ (((5867731/114810000) : ℚ) : ℝ)) := by
  rw [G41_6_formula]
  exact vasyuninBEntry_6_41_eval

def interval_41_6 : NamedVasyuninInterval :=
{
  h := 41
  k := 6
  lower := (5844769/114810000)
  upper := (5867731/114810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_6_interval
}

theorem G41_7_formula : baezDuarteGramEntry 41 7 = vasyuninBEntry 7 41 := by
  rw [baezDuarteGramEntry_symm 41 7]
  exact G7_41_formula

theorem G41_7_interval :
    ((((8067557/164430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 7) ∧
    (baezDuarteGramEntry 41 7 ≤ (((8100443/164430000) : ℚ) : ℝ)) := by
  rw [G41_7_formula]
  exact vasyuninBEntry_7_41_eval

def interval_41_7 : NamedVasyuninInterval :=
{
  h := 41
  k := 7
  lower := (8067557/164430000)
  upper := (8100443/164430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_7_interval
}

theorem G41_8_formula : baezDuarteGramEntry 41 8 = vasyuninBEntry 8 41 := by
  rw [baezDuarteGramEntry_symm 41 8]
  exact G8_41_formula

theorem G41_8_interval :
    ((((5499673/115770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 8) ∧
    (baezDuarteGramEntry 41 8 ≤ (((5522827/115770000) : ℚ) : ℝ)) := by
  rw [G41_8_formula]
  exact vasyuninBEntry_8_41_eval

def interval_41_8 : NamedVasyuninInterval :=
{
  h := 41
  k := 8
  lower := (5499673/115770000)
  upper := (5522827/115770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_8_interval
}

theorem G41_9_formula : baezDuarteGramEntry 41 9 = vasyuninBEntry 9 41 := by
  rw [baezDuarteGramEntry_symm 41 9]
  exact G9_41_formula

theorem G41_9_interval :
    ((((45740069/999310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 9) ∧
    (baezDuarteGramEntry 41 9 ≤ (((45939931/999310000) : ℚ) : ℝ)) := by
  rw [G41_9_formula]
  exact vasyuninBEntry_9_41_eval

def interval_41_9 : NamedVasyuninInterval :=
{
  h := 41
  k := 9
  lower := (45740069/999310000)
  upper := (45939931/999310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_9_interval
}

theorem G41_10_formula : baezDuarteGramEntry 41 10 = vasyuninBEntry 10 41 := by
  rw [baezDuarteGramEntry_symm 41 10]
  exact G10_41_formula

theorem G41_10_interval :
    ((((40180489/895110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 10) ∧
    (baezDuarteGramEntry 41 10 ≤ (((40359511/895110000) : ℚ) : ℝ)) := by
  rw [G41_10_formula]
  exact vasyuninBEntry_10_41_eval

def interval_41_10 : NamedVasyuninInterval :=
{
  h := 41
  k := 10
  lower := (40180489/895110000)
  upper := (40359511/895110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_10_interval
}

theorem G41_11_formula : baezDuarteGramEntry 41 11 = vasyuninBEntry 11 41 := by
  rw [baezDuarteGramEntry_symm 41 11]
  exact G11_41_formula

theorem G41_11_interval :
    ((((6439141/148590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 11) ∧
    (baezDuarteGramEntry 41 11 ≤ (((6468859/148590000) : ℚ) : ℝ)) := by
  rw [G41_11_formula]
  exact vasyuninBEntry_11_41_eval

def interval_41_11 : NamedVasyuninInterval :=
{
  h := 41
  k := 11
  lower := (6439141/148590000)
  upper := (6468859/148590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_11_interval
}

theorem G41_12_formula : baezDuarteGramEntry 41 12 = vasyuninBEntry 12 41 := by
  rw [baezDuarteGramEntry_symm 41 12]
  exact G12_41_formula

theorem G41_12_interval :
    ((((892261/21140000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 12) ∧
    (baezDuarteGramEntry 41 12 ≤ (((896489/21140000) : ℚ) : ℝ)) := by
  rw [G41_12_formula]
  exact vasyuninBEntry_12_41_eval

def interval_41_12 : NamedVasyuninInterval :=
{
  h := 41
  k := 12
  lower := (892261/21140000)
  upper := (896489/21140000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_12_interval
}

theorem G41_13_formula : baezDuarteGramEntry 41 13 = vasyuninBEntry 13 41 := by
  rw [baezDuarteGramEntry_symm 41 13]
  exact G13_41_formula

theorem G41_13_interval :
    ((((1534309/36910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 13) ∧
    (baezDuarteGramEntry 41 13 ≤ (((1541691/36910000) : ℚ) : ℝ)) := by
  rw [G41_13_formula]
  exact vasyuninBEntry_13_41_eval

def interval_41_13 : NamedVasyuninInterval :=
{
  h := 41
  k := 13
  lower := (1534309/36910000)
  upper := (1541691/36910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_13_interval
}

theorem G41_14_formula : baezDuarteGramEntry 41 14 = vasyuninBEntry 14 41 := by
  rw [baezDuarteGramEntry_symm 41 14]
  exact G14_41_formula

theorem G41_14_interval :
    ((((38875081/949190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 14) ∧
    (baezDuarteGramEntry 41 14 ≤ (((39064919/949190000) : ℚ) : ℝ)) := by
  rw [G41_14_formula]
  exact vasyuninBEntry_14_41_eval

def interval_41_14 : NamedVasyuninInterval :=
{
  h := 41
  k := 14
  lower := (38875081/949190000)
  upper := (39064919/949190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_14_interval
}

theorem G41_15_formula : baezDuarteGramEntry 41 15 = vasyuninBEntry 15 41 := by
  rw [baezDuarteGramEntry_symm 41 15]
  exact G15_41_formula

theorem G41_15_interval :
    ((((34372949/870510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 15) ∧
    (baezDuarteGramEntry 41 15 ≤ (((34547051/870510000) : ℚ) : ℝ)) := by
  rw [G41_15_formula]
  exact vasyuninBEntry_15_41_eval

def interval_41_15 : NamedVasyuninInterval :=
{
  h := 41
  k := 15
  lower := (34372949/870510000)
  upper := (34547051/870510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_15_interval
}

theorem G41_16_formula : baezDuarteGramEntry 41 16 = vasyuninBEntry 16 41 := by
  rw [baezDuarteGramEntry_symm 41 16]
  exact G16_41_formula

theorem G41_16_interval :
    ((((4620031/119690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 16) ∧
    (baezDuarteGramEntry 41 16 ≤ (((4643969/119690000) : ℚ) : ℝ)) := by
  rw [G41_16_formula]
  exact vasyuninBEntry_16_41_eval

def interval_41_16 : NamedVasyuninInterval :=
{
  h := 41
  k := 16
  lower := (4620031/119690000)
  upper := (4643969/119690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_16_interval
}

theorem G41_17_formula : baezDuarteGramEntry 41 17 = vasyuninBEntry 17 41 := by
  rw [baezDuarteGramEntry_symm 41 17]
  exact G17_41_formula

theorem G41_17_interval :
    ((((22031821/581790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 17) ∧
    (baezDuarteGramEntry 41 17 ≤ (((22148179/581790000) : ℚ) : ℝ)) := by
  rw [G41_17_formula]
  exact vasyuninBEntry_17_41_eval

def interval_41_17 : NamedVasyuninInterval :=
{
  h := 41
  k := 17
  lower := (22031821/581790000)
  upper := (22148179/581790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_17_interval
}

theorem G41_18_formula : baezDuarteGramEntry 41 18 = vasyuninBEntry 18 41 := by
  rw [baezDuarteGramEntry_symm 41 18]
  exact G18_41_formula

theorem G41_18_interval :
    ((((25242343/676570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 18) ∧
    (baezDuarteGramEntry 41 18 ≤ (((25377657/676570000) : ℚ) : ℝ)) := by
  rw [G41_18_formula]
  exact vasyuninBEntry_18_41_eval

def interval_41_18 : NamedVasyuninInterval :=
{
  h := 41
  k := 18
  lower := (25242343/676570000)
  upper := (25377657/676570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_18_interval
}

theorem G41_19_formula : baezDuarteGramEntry 41 19 = vasyuninBEntry 19 41 := by
  rw [baezDuarteGramEntry_symm 41 19]
  exact G19_41_formula

theorem G41_19_interval :
    ((((31435011/849890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 19) ∧
    (baezDuarteGramEntry 41 19 ≤ (((31604989/849890000) : ℚ) : ℝ)) := by
  rw [G41_19_formula]
  exact vasyuninBEntry_19_41_eval

def interval_41_19 : NamedVasyuninInterval :=
{
  h := 41
  k := 19
  lower := (31435011/849890000)
  upper := (31604989/849890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_19_interval
}

theorem G41_20_formula : baezDuarteGramEntry 41 20 = vasyuninBEntry 20 41 := by
  rw [baezDuarteGramEntry_symm 41 20]
  exact G20_41_formula

theorem G41_20_interval :
    ((((10003013/269870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 20) ∧
    (baezDuarteGramEntry 41 20 ≤ (((10056987/269870000) : ℚ) : ℝ)) := by
  rw [G41_20_formula]
  exact vasyuninBEntry_20_41_eval

def interval_41_20 : NamedVasyuninInterval :=
{
  h := 41
  k := 20
  lower := (10003013/269870000)
  upper := (10056987/269870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_20_interval
}

theorem G41_21_formula : baezDuarteGramEntry 41 21 = vasyuninBEntry 21 41 := by
  rw [baezDuarteGramEntry_symm 41 21]
  exact G21_41_formula

theorem G41_21_interval :
    ((((12096789/332110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 21) ∧
    (baezDuarteGramEntry 41 21 ≤ (((12163211/332110000) : ℚ) : ℝ)) := by
  rw [G41_21_formula]
  exact vasyuninBEntry_21_41_eval

def interval_41_21 : NamedVasyuninInterval :=
{
  h := 41
  k := 21
  lower := (12096789/332110000)
  upper := (12163211/332110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_21_interval
}

theorem G41_22_formula : baezDuarteGramEntry 41 22 = vasyuninBEntry 22 41 := by
  rw [baezDuarteGramEntry_symm 41 22]
  exact G22_41_formula

theorem G41_22_interval :
    ((((27800853/791470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 22) ∧
    (baezDuarteGramEntry 41 22 ≤ (((27959147/791470000) : ℚ) : ℝ)) := by
  rw [G41_22_formula]
  exact vasyuninBEntry_22_41_eval

def interval_41_22 : NamedVasyuninInterval :=
{
  h := 41
  k := 22
  lower := (27800853/791470000)
  upper := (27959147/791470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_22_interval
}

theorem G41_23_formula : baezDuarteGramEntry 41 23 = vasyuninBEntry 23 41 := by
  rw [baezDuarteGramEntry_symm 41 23]
  exact G23_41_formula

theorem G41_23_interval :
    ((((31268649/913510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 23) ∧
    (baezDuarteGramEntry 41 23 ≤ (((31451351/913510000) : ℚ) : ℝ)) := by
  rw [G41_23_formula]
  exact vasyuninBEntry_23_41_eval

def interval_41_23 : NamedVasyuninInterval :=
{
  h := 41
  k := 23
  lower := (31268649/913510000)
  upper := (31451351/913510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_23_interval
}

theorem G41_24_formula : baezDuarteGramEntry 41 24 = vasyuninBEntry 24 41 := by
  rw [baezDuarteGramEntry_symm 41 24]
  exact G24_41_formula

theorem G41_24_interval :
    ((((27677457/825430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 24) ∧
    (baezDuarteGramEntry 41 24 ≤ (((27842543/825430000) : ℚ) : ℝ)) := by
  rw [G41_24_formula]
  exact vasyuninBEntry_24_41_eval

def interval_41_24 : NamedVasyuninInterval :=
{
  h := 41
  k := 24
  lower := (27677457/825430000)
  upper := (27842543/825430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_24_interval
}

theorem G41_25_formula : baezDuarteGramEntry 41 25 = vasyuninBEntry 25 41 := by
  rw [baezDuarteGramEntry_symm 41 25]
  exact G25_41_formula

theorem G41_25_interval :
    ((((2472497/75030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 25) ∧
    (baezDuarteGramEntry 41 25 ≤ (((2487503/75030000) : ℚ) : ℝ)) := by
  rw [G41_25_formula]
  exact vasyuninBEntry_25_41_eval

def interval_41_25 : NamedVasyuninInterval :=
{
  h := 41
  k := 25
  lower := (2472497/75030000)
  upper := (2487503/75030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_25_interval
}

theorem G41_26_formula : baezDuarteGramEntry 41 26 = vasyuninBEntry 26 41 := by
  rw [baezDuarteGramEntry_symm 41 26]
  exact G26_41_formula

theorem G41_26_interval :
    ((((439583/13545000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 26) ∧
    (baezDuarteGramEntry 41 26 ≤ (((110573/3386250) : ℚ) : ℝ)) := by
  rw [G41_26_formula]
  exact vasyuninBEntry_26_41_eval

def interval_41_26 : NamedVasyuninInterval :=
{
  h := 41
  k := 26
  lower := (439583/13545000)
  upper := (110573/3386250)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_26_interval
}

theorem G41_27_formula : baezDuarteGramEntry 41 27 = vasyuninBEntry 27 41 := by
  rw [baezDuarteGramEntry_symm 41 27]
  exact G27_41_formula

theorem G41_27_interval :
    ((((3828091/119090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 27) ∧
    (baezDuarteGramEntry 41 27 ≤ (((3851909/119090000) : ℚ) : ℝ)) := by
  rw [G41_27_formula]
  exact vasyuninBEntry_27_41_eval

def interval_41_27 : NamedVasyuninInterval :=
{
  h := 41
  k := 27
  lower := (3828091/119090000)
  upper := (3851909/119090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_27_interval
}

theorem G41_28_formula : baezDuarteGramEntry 41 28 = vasyuninBEntry 28 41 := by
  rw [baezDuarteGramEntry_symm 41 28]
  exact G28_41_formula

theorem G41_28_interval :
    ((((30324157/958430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 28) ∧
    (baezDuarteGramEntry 41 28 ≤ (((30515843/958430000) : ℚ) : ℝ)) := by
  rw [G41_28_formula]
  exact vasyuninBEntry_28_41_eval

def interval_41_28 : NamedVasyuninInterval :=
{
  h := 41
  k := 28
  lower := (30324157/958430000)
  upper := (30515843/958430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_28_interval
}

theorem G41_29_formula : baezDuarteGramEntry 41 29 = vasyuninBEntry 29 41 := by
  rw [baezDuarteGramEntry_symm 41 29]
  exact G29_41_formula

theorem G41_29_interval :
    ((((27980213/897870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 29) ∧
    (baezDuarteGramEntry 41 29 ≤ (((28159787/897870000) : ℚ) : ℝ)) := by
  rw [G41_29_formula]
  exact vasyuninBEntry_29_41_eval

def interval_41_29 : NamedVasyuninInterval :=
{
  h := 41
  k := 29
  lower := (27980213/897870000)
  upper := (28159787/897870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_29_interval
}

theorem G41_30_formula : baezDuarteGramEntry 41 30 = vasyuninBEntry 30 41 := by
  rw [baezDuarteGramEntry_symm 41 30]
  exact G30_41_formula

theorem G41_30_interval :
    ((((184521/5990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 30) ∧
    (baezDuarteGramEntry 41 30 ≤ (((185719/5990000) : ℚ) : ℝ)) := by
  rw [G41_30_formula]
  exact vasyuninBEntry_30_41_eval

def interval_41_30 : NamedVasyuninInterval :=
{
  h := 41
  k := 30
  lower := (184521/5990000)
  upper := (185719/5990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_30_interval
}

theorem G41_31_formula : baezDuarteGramEntry 41 31 = vasyuninBEntry 31 41 := by
  rw [baezDuarteGramEntry_symm 41 31]
  exact G31_41_formula

theorem G41_31_interval :
    ((((3650543/119570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 31) ∧
    (baezDuarteGramEntry 41 31 ≤ (((3674457/119570000) : ℚ) : ℝ)) := by
  rw [G41_31_formula]
  exact vasyuninBEntry_31_41_eval

def interval_41_31 : NamedVasyuninInterval :=
{
  h := 41
  k := 31
  lower := (3650543/119570000)
  upper := (3674457/119570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_31_interval
}

theorem G41_32_formula : baezDuarteGramEntry 41 32 = vasyuninBEntry 32 41 := by
  rw [baezDuarteGramEntry_symm 41 32]
  exact G32_41_formula

theorem G41_32_interval :
    ((((3695267/122330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 32) ∧
    (baezDuarteGramEntry 41 32 ≤ (((3719733/122330000) : ℚ) : ℝ)) := by
  rw [G41_32_formula]
  exact vasyuninBEntry_32_41_eval

def interval_41_32 : NamedVasyuninInterval :=
{
  h := 41
  k := 32
  lower := (3695267/122330000)
  upper := (3719733/122330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_32_interval
}

theorem G41_33_formula : baezDuarteGramEntry 41 33 = vasyuninBEntry 33 41 := by
  rw [baezDuarteGramEntry_symm 41 33]
  exact G33_41_formula

theorem G41_33_interval :
    ((((12892011/429890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 33) ∧
    (baezDuarteGramEntry 41 33 ≤ (((12977989/429890000) : ℚ) : ℝ)) := by
  rw [G41_33_formula]
  exact vasyuninBEntry_33_41_eval

def interval_41_33 : NamedVasyuninInterval :=
{
  h := 41
  k := 33
  lower := (12892011/429890000)
  upper := (12977989/429890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_33_interval
}

theorem G41_34_formula : baezDuarteGramEntry 41 34 = vasyuninBEntry 34 41 := by
  rw [baezDuarteGramEntry_symm 41 34]
  exact G34_41_formula

theorem G41_34_interval :
    ((((1209689/40610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 34) ∧
    (baezDuarteGramEntry 41 34 ≤ (((1217811/40610000) : ℚ) : ℝ)) := by
  rw [G41_34_formula]
  exact vasyuninBEntry_34_41_eval

def interval_41_34 : NamedVasyuninInterval :=
{
  h := 41
  k := 34
  lower := (1209689/40610000)
  upper := (1217811/40610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_34_interval
}

theorem G41_35_formula : baezDuarteGramEntry 41 35 = vasyuninBEntry 35 41 := by
  rw [baezDuarteGramEntry_symm 41 35]
  exact G35_41_formula

theorem G41_35_interval :
    ((((14979463/505370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 35) ∧
    (baezDuarteGramEntry 41 35 ≤ (((15080537/505370000) : ℚ) : ℝ)) := by
  rw [G41_35_formula]
  exact vasyuninBEntry_35_41_eval

def interval_41_35 : NamedVasyuninInterval :=
{
  h := 41
  k := 35
  lower := (14979463/505370000)
  upper := (15080537/505370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_35_interval
}

theorem G41_36_formula : baezDuarteGramEntry 41 36 = vasyuninBEntry 36 41 := by
  rw [baezDuarteGramEntry_symm 41 36]
  exact G36_41_formula

theorem G41_36_interval :
    ((((2023153/68470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 36) ∧
    (baezDuarteGramEntry 41 36 ≤ (((2036847/68470000) : ℚ) : ℝ)) := by
  rw [G41_36_formula]
  exact vasyuninBEntry_36_41_eval

def interval_41_36 : NamedVasyuninInterval :=
{
  h := 41
  k := 36
  lower := (2023153/68470000)
  upper := (2036847/68470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_36_interval
}

theorem G41_37_formula : baezDuarteGramEntry 41 37 = vasyuninBEntry 37 41 := by
  rw [baezDuarteGramEntry_symm 41 37]
  exact G37_41_formula

theorem G41_37_interval :
    ((((14660331/496690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 37) ∧
    (baezDuarteGramEntry 41 37 ≤ (((14759669/496690000) : ℚ) : ℝ)) := by
  rw [G41_37_formula]
  exact vasyuninBEntry_37_41_eval

def interval_41_37 : NamedVasyuninInterval :=
{
  h := 41
  k := 37
  lower := (14660331/496690000)
  upper := (14759669/496690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_37_interval
}

theorem G41_38_formula : baezDuarteGramEntry 41 38 = vasyuninBEntry 38 41 := by
  rw [baezDuarteGramEntry_symm 41 38]
  exact G38_41_formula

theorem G41_38_interval :
    ((((29460329/996710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 38) ∧
    (baezDuarteGramEntry 41 38 ≤ (((29659671/996710000) : ℚ) : ℝ)) := by
  rw [G41_38_formula]
  exact vasyuninBEntry_38_41_eval

def interval_41_38 : NamedVasyuninInterval :=
{
  h := 41
  k := 38
  lower := (29460329/996710000)
  upper := (29659671/996710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_38_interval
}

theorem G41_39_formula : baezDuarteGramEntry 41 39 = vasyuninBEntry 39 41 := by
  rw [baezDuarteGramEntry_symm 41 39]
  exact G39_41_formula

theorem G41_39_interval :
    ((((908503/30595000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 39) ∧
    (baezDuarteGramEntry 41 39 ≤ (((457311/15297500) : ℚ) : ℝ)) := by
  rw [G41_39_formula]
  exact vasyuninBEntry_39_41_eval

def interval_41_39 : NamedVasyuninInterval :=
{
  h := 41
  k := 39
  lower := (908503/30595000)
  upper := (457311/15297500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_39_interval
}

theorem G41_40_formula : baezDuarteGramEntry 41 40 = vasyuninBEntry 40 41 := by
  rw [baezDuarteGramEntry_symm 41 40]
  exact G40_41_formula

theorem G41_40_interval :
    ((((24418539/814610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 40) ∧
    (baezDuarteGramEntry 41 40 ≤ (((24581461/814610000) : ℚ) : ℝ)) := by
  rw [G41_40_formula]
  exact vasyuninBEntry_40_41_eval

def interval_41_40 : NamedVasyuninInterval :=
{
  h := 41
  k := 40
  lower := (24418539/814610000)
  upper := (24581461/814610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_40_interval
}

theorem G41_41_formula_eq : baezDuarteGramEntry 41 41 = (1 / (41 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 41 := by norm_num
  rw [baez_duarte_diagonal_scaling 41 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G41_41_log_gamma_interval :
  ((((21380239/697610000) : ℚ) : ℝ) ≤ (1 / (41 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (41 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((21519761/697610000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 41 (by norm_num)
  constructor
  · have : ((((21380239/697610000) : ℚ) : ℝ) ≤ (1 / (41 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (41 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((21519761/697610000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G41_41_interval : ((((21380239/697610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 41) ∧ (baezDuarteGramEntry 41 41 ≤ (((21519761/697610000) : ℚ) : ℝ)) := by
  rw [G41_41_formula_eq]
  exact G41_41_log_gamma_interval

def interval_41_41 : NamedVasyuninInterval :=
{
  h := 41
  k := 41
  lower := (21380239/697610000)
  upper := (21519761/697610000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G41_41_interval
}

theorem G41_42_formula : baezDuarteGramEntry 41 42 = vasyuninBEntry 41 42 := vasyuninBEntry_correct_axiom 41 42

theorem vasyuninBEntry_41_42_eval :
    ((((2251059/76910000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 42) ∧
    (vasyuninBEntry 41 42 ≤ (((2266441/76910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4142_formula_bound
  constructor <;> linarith

theorem G41_42_interval :
    ((((2251059/76910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 42) ∧
    (baezDuarteGramEntry 41 42 ≤ (((2266441/76910000) : ℚ) : ℝ)) := by
  rw [G41_42_formula]
  exact vasyuninBEntry_41_42_eval

def interval_41_42 : NamedVasyuninInterval :=
{
  h := 41
  k := 42
  lower := (2251059/76910000)
  upper := (2266441/76910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_42_interval
}

theorem G41_43_formula : baezDuarteGramEntry 41 43 = vasyuninBEntry 41 43 := vasyuninBEntry_correct_axiom 41 43

theorem vasyuninBEntry_41_43_eval :
    ((((23098457/815430000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 43) ∧
    (vasyuninBEntry 41 43 ≤ (((23261543/815430000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4143_formula_bound
  constructor <;> linarith

theorem G41_43_interval :
    ((((23098457/815430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 43) ∧
    (baezDuarteGramEntry 41 43 ≤ (((23261543/815430000) : ℚ) : ℝ)) := by
  rw [G41_43_formula]
  exact vasyuninBEntry_41_43_eval

def interval_41_43 : NamedVasyuninInterval :=
{
  h := 41
  k := 43
  lower := (23098457/815430000)
  upper := (23261543/815430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_43_interval
}

theorem G41_44_formula : baezDuarteGramEntry 41 44 = vasyuninBEntry 41 44 := vasyuninBEntry_correct_axiom 41 44

theorem vasyuninBEntry_41_44_eval :
    ((((2923141/106090000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 44) ∧
    (vasyuninBEntry 41 44 ≤ (((2944359/106090000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4144_formula_bound
  constructor <;> linarith

theorem G41_44_interval :
    ((((2923141/106090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 44) ∧
    (baezDuarteGramEntry 41 44 ≤ (((2944359/106090000) : ℚ) : ℝ)) := by
  rw [G41_44_formula]
  exact vasyuninBEntry_41_44_eval

def interval_41_44 : NamedVasyuninInterval :=
{
  h := 41
  k := 44
  lower := (2923141/106090000)
  upper := (2944359/106090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_44_interval
}

theorem G41_45_formula : baezDuarteGramEntry 41 45 = vasyuninBEntry 41 45 := vasyuninBEntry_correct_axiom 41 45

theorem vasyuninBEntry_41_45_eval :
    ((((3708209/137910000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 45) ∧
    (vasyuninBEntry 41 45 ≤ (((3735791/137910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4145_formula_bound
  constructor <;> linarith

theorem G41_45_interval :
    ((((3708209/137910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 45) ∧
    (baezDuarteGramEntry 41 45 ≤ (((3735791/137910000) : ℚ) : ℝ)) := by
  rw [G41_45_formula]
  exact vasyuninBEntry_41_45_eval

def interval_41_45 : NamedVasyuninInterval :=
{
  h := 41
  k := 45
  lower := (3708209/137910000)
  upper := (3735791/137910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_45_interval
}

theorem G41_46_formula : baezDuarteGramEntry 41 46 = vasyuninBEntry 41 46 := vasyuninBEntry_correct_axiom 41 46

theorem vasyuninBEntry_41_46_eval :
    ((((13448869/511310000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 46) ∧
    (vasyuninBEntry 41 46 ≤ (((13551131/511310000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4146_formula_bound
  constructor <;> linarith

theorem G41_46_interval :
    ((((13448869/511310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 46) ∧
    (baezDuarteGramEntry 41 46 ≤ (((13551131/511310000) : ℚ) : ℝ)) := by
  rw [G41_46_formula]
  exact vasyuninBEntry_41_46_eval

def interval_41_46 : NamedVasyuninInterval :=
{
  h := 41
  k := 46
  lower := (13448869/511310000)
  upper := (13551131/511310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_46_interval
}

theorem G41_47_formula : baezDuarteGramEntry 41 47 = vasyuninBEntry 41 47 := vasyuninBEntry_correct_axiom 41 47

theorem vasyuninBEntry_41_47_eval :
    ((((22682009/879910000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 47) ∧
    (vasyuninBEntry 41 47 ≤ (((22857991/879910000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4147_formula_bound
  constructor <;> linarith

theorem G41_47_interval :
    ((((22682009/879910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 47) ∧
    (baezDuarteGramEntry 41 47 ≤ (((22857991/879910000) : ℚ) : ℝ)) := by
  rw [G41_47_formula]
  exact vasyuninBEntry_41_47_eval

def interval_41_47 : NamedVasyuninInterval :=
{
  h := 41
  k := 47
  lower := (22682009/879910000)
  upper := (22857991/879910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_47_interval
}

theorem G41_48_formula : baezDuarteGramEntry 41 48 = vasyuninBEntry 41 48 := vasyuninBEntry_correct_axiom 41 48

theorem vasyuninBEntry_41_48_eval :
    ((((16534651/653490000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 48) ∧
    (vasyuninBEntry 41 48 ≤ (((16665349/653490000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4148_formula_bound
  constructor <;> linarith

theorem G41_48_interval :
    ((((16534651/653490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 48) ∧
    (baezDuarteGramEntry 41 48 ≤ (((16665349/653490000) : ℚ) : ℝ)) := by
  rw [G41_48_formula]
  exact vasyuninBEntry_41_48_eval

def interval_41_48 : NamedVasyuninInterval :=
{
  h := 41
  k := 48
  lower := (16534651/653490000)
  upper := (16665349/653490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_48_interval
}

theorem G41_49_formula : baezDuarteGramEntry 41 49 = vasyuninBEntry 41 49 := vasyuninBEntry_correct_axiom 41 49

theorem vasyuninBEntry_41_49_eval :
    ((((4173219/167810000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 49) ∧
    (vasyuninBEntry 41 49 ≤ (((4206781/167810000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4149_formula_bound
  constructor <;> linarith

theorem G41_49_interval :
    ((((4173219/167810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 49) ∧
    (baezDuarteGramEntry 41 49 ≤ (((4206781/167810000) : ℚ) : ℝ)) := by
  rw [G41_49_formula]
  exact vasyuninBEntry_41_49_eval

def interval_41_49 : NamedVasyuninInterval :=
{
  h := 41
  k := 49
  lower := (4173219/167810000)
  upper := (4206781/167810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_49_interval
}

theorem G41_50_formula : baezDuarteGramEntry 41 50 = vasyuninBEntry 41 50 := vasyuninBEntry_correct_axiom 41 50

theorem vasyuninBEntry_41_50_eval :
    ((((22059803/901970000) : ℚ) : ℝ) ≤ vasyuninBEntry 41 50) ∧
    (vasyuninBEntry 41 50 ≤ (((22240197/901970000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4150_formula_bound
  constructor <;> linarith

theorem G41_50_interval :
    ((((22059803/901970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 41 50) ∧
    (baezDuarteGramEntry 41 50 ≤ (((22240197/901970000) : ℚ) : ℝ)) := by
  rw [G41_50_formula]
  exact vasyuninBEntry_41_50_eval

def interval_41_50 : NamedVasyuninInterval :=
{
  h := 41
  k := 50
  lower := (22059803/901970000)
  upper := (22240197/901970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G41_50_interval
}

theorem G42_1_formula : baezDuarteGramEntry 42 1 = vasyuninBEntry 1 42 := by
  rw [baezDuarteGramEntry_symm 42 1]
  exact G1_42_formula

theorem G42_1_interval :
    ((((1234271/17290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 1) ∧
    (baezDuarteGramEntry 42 1 ≤ (((1237729/17290000) : ℚ) : ℝ)) := by
  rw [G42_1_formula]
  exact vasyuninBEntry_1_42_eval

def interval_42_1 : NamedVasyuninInterval :=
{
  h := 42
  k := 1
  lower := (1234271/17290000)
  upper := (1237729/17290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_1_interval
}

theorem G42_2_formula : baezDuarteGramEntry 42 2 = vasyuninBEntry 2 42 := by
  rw [baezDuarteGramEntry_symm 42 2]
  exact G2_42_formula

theorem G42_2_interval :
    ((((5320583/84170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 42 2) ∧
    (baezDuarteGramEntry 42 2 ≤ (((5337417/84170000) : ℚ) : ℝ)) := by
  rw [G42_2_formula]
  exact vasyuninBEntry_2_42_eval

def interval_42_2 : NamedVasyuninInterval :=
{
  h := 42
  k := 2
  lower := (5320583/84170000)
  upper := (5337417/84170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G42_2_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
