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
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part9
import RiemannHypothesis.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50_Part10

namespace RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
open RH.Criteria.NymanBeurling.VasyuninGram
open RH.Certificates.Generated

theorem G46_31_formula : baezDuarteGramEntry 46 31 = vasyuninBEntry 31 46 := by
  rw [baezDuarteGramEntry_symm 46 31]
  exact G31_46_formula

theorem G46_31_interval :
    ((((7608217/267830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 31) ∧
    (baezDuarteGramEntry 46 31 ≤ (((7661783/267830000) : ℚ) : ℝ)) := by
  rw [G46_31_formula]
  exact vasyuninBEntry_31_46_eval

def interval_46_31 : NamedVasyuninInterval :=
{
  h := 46
  k := 31
  lower := (7608217/267830000)
  upper := (7661783/267830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_31_interval
}

theorem G46_32_formula : baezDuarteGramEntry 46 32 = vasyuninBEntry 32 46 := by
  rw [baezDuarteGramEntry_symm 46 32]
  exact G32_46_formula

theorem G46_32_interval :
    ((((5154059/184410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 32) ∧
    (baezDuarteGramEntry 46 32 ≤ (((5190941/184410000) : ℚ) : ℝ)) := by
  rw [G46_32_formula]
  exact vasyuninBEntry_32_46_eval

def interval_46_32 : NamedVasyuninInterval :=
{
  h := 46
  k := 32
  lower := (5154059/184410000)
  upper := (5190941/184410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_32_interval
}

theorem G46_33_formula : baezDuarteGramEntry 46 33 = vasyuninBEntry 33 46 := by
  rw [baezDuarteGramEntry_symm 46 33]
  exact G33_46_formula

theorem G46_33_interval :
    ((((215221/7790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 33) ∧
    (baezDuarteGramEntry 46 33 ≤ (((216779/7790000) : ℚ) : ℝ)) := by
  rw [G46_33_formula]
  exact vasyuninBEntry_33_46_eval

def interval_46_33 : NamedVasyuninInterval :=
{
  h := 46
  k := 33
  lower := (215221/7790000)
  upper := (216779/7790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_33_interval
}

theorem G46_34_formula : baezDuarteGramEntry 46 34 = vasyuninBEntry 34 46 := by
  rw [baezDuarteGramEntry_symm 46 34]
  exact G34_46_formula

theorem G46_34_interval :
    ((((928483/33920000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 34) ∧
    (baezDuarteGramEntry 46 34 ≤ (((935267/33920000) : ℚ) : ℝ)) := by
  rw [G46_34_formula]
  exact vasyuninBEntry_34_46_eval

def interval_46_34 : NamedVasyuninInterval :=
{
  h := 46
  k := 34
  lower := (928483/33920000)
  upper := (935267/33920000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_34_interval
}

theorem G46_35_formula : baezDuarteGramEntry 46 35 = vasyuninBEntry 35 46 := by
  rw [baezDuarteGramEntry_symm 46 35]
  exact G35_46_formula

theorem G46_35_interval :
    ((((26980551/994490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 35) ∧
    (baezDuarteGramEntry 46 35 ≤ (((27179449/994490000) : ℚ) : ℝ)) := by
  rw [G46_35_formula]
  exact vasyuninBEntry_35_46_eval

def interval_46_35 : NamedVasyuninInterval :=
{
  h := 46
  k := 35
  lower := (26980551/994490000)
  upper := (27179449/994490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_35_interval
}

theorem G46_36_formula : baezDuarteGramEntry 46 36 = vasyuninBEntry 36 46 := by
  rw [baezDuarteGramEntry_symm 46 36]
  exact G36_46_formula

theorem G46_36_interval :
    ((((26083011/969890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 36) ∧
    (baezDuarteGramEntry 46 36 ≤ (((26276989/969890000) : ℚ) : ℝ)) := by
  rw [G46_36_formula]
  exact vasyuninBEntry_36_46_eval

def interval_46_36 : NamedVasyuninInterval :=
{
  h := 46
  k := 36
  lower := (26083011/969890000)
  upper := (26276989/969890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_36_interval
}

theorem G46_37_formula : baezDuarteGramEntry 46 37 = vasyuninBEntry 37 46 := by
  rw [baezDuarteGramEntry_symm 46 37]
  exact G37_46_formula

theorem G46_37_interval :
    ((((2647593/99070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 37) ∧
    (baezDuarteGramEntry 46 37 ≤ (((2667407/99070000) : ℚ) : ℝ)) := by
  rw [G46_37_formula]
  exact vasyuninBEntry_37_46_eval

def interval_46_37 : NamedVasyuninInterval :=
{
  h := 46
  k := 37
  lower := (2647593/99070000)
  upper := (2667407/99070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_37_interval
}

theorem G46_38_formula : baezDuarteGramEntry 46 38 = vasyuninBEntry 38 46 := by
  rw [baezDuarteGramEntry_symm 46 38]
  exact G38_46_formula

theorem G46_38_interval :
    ((((7048457/265430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 38) ∧
    (baezDuarteGramEntry 46 38 ≤ (((7101543/265430000) : ℚ) : ℝ)) := by
  rw [G46_38_formula]
  exact vasyuninBEntry_38_46_eval

def interval_46_38 : NamedVasyuninInterval :=
{
  h := 46
  k := 38
  lower := (7048457/265430000)
  upper := (7101543/265430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_38_interval
}

theorem G46_39_formula : baezDuarteGramEntry 46 39 = vasyuninBEntry 39 46 := by
  rw [baezDuarteGramEntry_symm 46 39]
  exact G39_46_formula

theorem G46_39_interval :
    ((((18370497/695030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 39) ∧
    (baezDuarteGramEntry 46 39 ≤ (((18509503/695030000) : ℚ) : ℝ)) := by
  rw [G46_39_formula]
  exact vasyuninBEntry_39_46_eval

def interval_46_39 : NamedVasyuninInterval :=
{
  h := 46
  k := 39
  lower := (18370497/695030000)
  upper := (18509503/695030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_39_interval
}

theorem G46_40_formula : baezDuarteGramEntry 46 40 = vasyuninBEntry 40 46 := by
  rw [baezDuarteGramEntry_symm 46 40]
  exact G40_46_formula

theorem G46_40_interval :
    ((((39553/1501250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 40) ∧
    (baezDuarteGramEntry 46 40 ≤ (((159413/6005000) : ℚ) : ℝ)) := by
  rw [G46_40_formula]
  exact vasyuninBEntry_40_46_eval

def interval_46_40 : NamedVasyuninInterval :=
{
  h := 46
  k := 40
  lower := (39553/1501250)
  upper := (159413/6005000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_40_interval
}

theorem G46_41_formula : baezDuarteGramEntry 46 41 = vasyuninBEntry 41 46 := by
  rw [baezDuarteGramEntry_symm 46 41]
  exact G41_46_formula

theorem G46_41_interval :
    ((((13448869/511310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 41) ∧
    (baezDuarteGramEntry 46 41 ≤ (((13551131/511310000) : ℚ) : ℝ)) := by
  rw [G46_41_formula]
  exact vasyuninBEntry_41_46_eval

def interval_46_41 : NamedVasyuninInterval :=
{
  h := 46
  k := 41
  lower := (13448869/511310000)
  upper := (13551131/511310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_41_interval
}

theorem G46_42_formula : baezDuarteGramEntry 46 42 = vasyuninBEntry 42 46 := by
  rw [baezDuarteGramEntry_symm 46 42]
  exact G42_46_formula

theorem G46_42_interval :
    ((((25303803/961970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 42) ∧
    (baezDuarteGramEntry 46 42 ≤ (((25496197/961970000) : ℚ) : ℝ)) := by
  rw [G46_42_formula]
  exact vasyuninBEntry_42_46_eval

def interval_46_42 : NamedVasyuninInterval :=
{
  h := 46
  k := 42
  lower := (25303803/961970000)
  upper := (25496197/961970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_42_interval
}

theorem G46_43_formula : baezDuarteGramEntry 46 43 = vasyuninBEntry 43 46 := by
  rw [baezDuarteGramEntry_symm 46 43]
  exact G43_46_formula

theorem G46_43_interval :
    ((((4626451/175490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 43) ∧
    (baezDuarteGramEntry 46 43 ≤ (((4661549/175490000) : ℚ) : ℝ)) := by
  rw [G46_43_formula]
  exact vasyuninBEntry_43_46_eval

def interval_46_43 : NamedVasyuninInterval :=
{
  h := 46
  k := 43
  lower := (4626451/175490000)
  upper := (4661549/175490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_43_interval
}

theorem G46_44_formula : baezDuarteGramEntry 46 44 = vasyuninBEntry 44 46 := by
  rw [baezDuarteGramEntry_symm 46 44]
  exact G44_46_formula

theorem G46_44_interval :
    ((((866729/32710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 44) ∧
    (baezDuarteGramEntry 46 44 ≤ (((873271/32710000) : ℚ) : ℝ)) := by
  rw [G46_44_formula]
  exact vasyuninBEntry_44_46_eval

def interval_46_44 : NamedVasyuninInterval :=
{
  h := 46
  k := 44
  lower := (866729/32710000)
  upper := (873271/32710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_44_interval
}

theorem G46_45_formula : baezDuarteGramEntry 46 45 = vasyuninBEntry 45 46 := by
  rw [baezDuarteGramEntry_symm 46 45]
  exact G45_46_formula

theorem G46_45_interval :
    ((((2506877/93730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 45) ∧
    (baezDuarteGramEntry 46 45 ≤ (((2525623/93730000) : ℚ) : ℝ)) := by
  rw [G46_45_formula]
  exact vasyuninBEntry_45_46_eval

def interval_46_45 : NamedVasyuninInterval :=
{
  h := 46
  k := 45
  lower := (2506877/93730000)
  upper := (2525623/93730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_45_interval
}

theorem G46_46_formula_eq : baezDuarteGramEntry 46 46 = (1 / (46 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 46 := by norm_num
  rw [baez_duarte_diagonal_scaling 46 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G46_46_log_gamma_interval :
  ((((5218389/191110000) : ℚ) : ℝ) ≤ (1 / (46 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (46 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((5256611/191110000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 46 (by norm_num)
  constructor
  · have : ((((5218389/191110000) : ℚ) : ℝ) ≤ (1 / (46 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (46 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((5256611/191110000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G46_46_interval : ((((5218389/191110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 46) ∧ (baezDuarteGramEntry 46 46 ≤ (((5256611/191110000) : ℚ) : ℝ)) := by
  rw [G46_46_formula_eq]
  exact G46_46_log_gamma_interval

def interval_46_46 : NamedVasyuninInterval :=
{
  h := 46
  k := 46
  lower := (5218389/191110000)
  upper := (5256611/191110000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G46_46_interval
}

theorem G46_47_formula : baezDuarteGramEntry 46 47 = vasyuninBEntry 46 47 := vasyuninBEntry_correct_axiom 46 47

theorem vasyuninBEntry_46_47_eval :
    ((((5531373/211270000) : ℚ) : ℝ) ≤ vasyuninBEntry 46 47) ∧
    (vasyuninBEntry 46 47 ≤ (((5573627/211270000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4647_formula_bound
  constructor <;> linarith

theorem G46_47_interval :
    ((((5531373/211270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 47) ∧
    (baezDuarteGramEntry 46 47 ≤ (((5573627/211270000) : ℚ) : ℝ)) := by
  rw [G46_47_formula]
  exact vasyuninBEntry_46_47_eval

def interval_46_47 : NamedVasyuninInterval :=
{
  h := 46
  k := 47
  lower := (5531373/211270000)
  upper := (5573627/211270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_47_interval
}

theorem G46_48_formula : baezDuarteGramEntry 46 48 = vasyuninBEntry 46 48 := vasyuninBEntry_correct_axiom 46 48

theorem vasyuninBEntry_46_48_eval :
    ((((10598281/417190000) : ℚ) : ℝ) ≤ vasyuninBEntry 46 48) ∧
    (vasyuninBEntry 46 48 ≤ (((10681719/417190000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_23_24_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 23 24 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G46_48_interval :
    ((((10598281/417190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 48) ∧
    (baezDuarteGramEntry 46 48 ≤ (((10681719/417190000) : ℚ) : ℝ)) := by
  rw [G46_48_formula]
  exact vasyuninBEntry_46_48_eval

def interval_46_48 : NamedVasyuninInterval :=
{
  h := 46
  k := 48
  lower := (10598281/417190000)
  upper := (10681719/417190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_48_interval
}

theorem G46_49_formula : baezDuarteGramEntry 46 49 = vasyuninBEntry 46 49 := vasyuninBEntry_correct_axiom 46 49

theorem vasyuninBEntry_46_49_eval :
    ((((15606967/630330000) : ℚ) : ℝ) ≤ vasyuninBEntry 46 49) ∧
    (vasyuninBEntry 46 49 ≤ (((15733033/630330000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4649_formula_bound
  constructor <;> linarith

theorem G46_49_interval :
    ((((15606967/630330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 49) ∧
    (baezDuarteGramEntry 46 49 ≤ (((15733033/630330000) : ℚ) : ℝ)) := by
  rw [G46_49_formula]
  exact vasyuninBEntry_46_49_eval

def interval_46_49 : NamedVasyuninInterval :=
{
  h := 46
  k := 49
  lower := (15606967/630330000)
  upper := (15733033/630330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_49_interval
}

theorem G46_50_formula : baezDuarteGramEntry 46 50 = vasyuninBEntry 46 50 := vasyuninBEntry_correct_axiom 46 50

theorem vasyuninBEntry_46_50_eval :
    ((((20335977/840230000) : ℚ) : ℝ) ≤ vasyuninBEntry 46 50) ∧
    (vasyuninBEntry 46 50 ≤ (((20504023/840230000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_23_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 23 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G46_50_interval :
    ((((20335977/840230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 46 50) ∧
    (baezDuarteGramEntry 46 50 ≤ (((20504023/840230000) : ℚ) : ℝ)) := by
  rw [G46_50_formula]
  exact vasyuninBEntry_46_50_eval

def interval_46_50 : NamedVasyuninInterval :=
{
  h := 46
  k := 50
  lower := (20335977/840230000)
  upper := (20504023/840230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G46_50_interval
}

theorem G47_1_formula : baezDuarteGramEntry 47 1 = vasyuninBEntry 1 47 := by
  rw [baezDuarteGramEntry_symm 47 1]
  exact G1_47_formula

theorem G47_1_interval :
    ((((10068503/154970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 1) ∧
    (baezDuarteGramEntry 47 1 ≤ (((10099497/154970000) : ℚ) : ℝ)) := by
  rw [G47_1_formula]
  exact vasyuninBEntry_1_47_eval

def interval_47_1 : NamedVasyuninInterval :=
{
  h := 47
  k := 1
  lower := (10068503/154970000)
  upper := (10099497/154970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_1_interval
}

theorem G47_2_formula : baezDuarteGramEntry 47 2 = vasyuninBEntry 2 47 := by
  rw [baezDuarteGramEntry_symm 47 2]
  exact G2_47_formula

theorem G47_2_interval :
    ((((1821633/31670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 2) ∧
    (baezDuarteGramEntry 47 2 ≤ (((1827967/31670000) : ℚ) : ℝ)) := by
  rw [G47_2_formula]
  exact vasyuninBEntry_2_47_eval

def interval_47_2 : NamedVasyuninInterval :=
{
  h := 47
  k := 2
  lower := (1821633/31670000)
  upper := (1827967/31670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_2_interval
}

theorem G47_3_formula : baezDuarteGramEntry 47 3 = vasyuninBEntry 3 47 := by
  rw [baezDuarteGramEntry_symm 47 3]
  exact G3_47_formula

theorem G47_3_interval :
    ((((289331/5440000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 3) ∧
    (baezDuarteGramEntry 47 3 ≤ (((290419/5440000) : ℚ) : ℝ)) := by
  rw [G47_3_formula]
  exact vasyuninBEntry_3_47_eval

def interval_47_3 : NamedVasyuninInterval :=
{
  h := 47
  k := 3
  lower := (289331/5440000)
  upper := (290419/5440000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_3_interval
}

theorem G47_4_formula : baezDuarteGramEntry 47 4 = vasyuninBEntry 4 47 := by
  rw [baezDuarteGramEntry_symm 47 4]
  exact G4_47_formula

theorem G47_4_interval :
    ((((5113/102000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 4) ∧
    (baezDuarteGramEntry 47 4 ≤ (((25667/510000) : ℚ) : ℝ)) := by
  rw [G47_4_formula]
  exact vasyuninBEntry_4_47_eval

def interval_47_4 : NamedVasyuninInterval :=
{
  h := 47
  k := 4
  lower := (5113/102000)
  upper := (25667/510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_4_interval
}

theorem G47_5_formula : baezDuarteGramEntry 47 5 = vasyuninBEntry 5 47 := by
  rw [baezDuarteGramEntry_symm 47 5]
  exact G5_47_formula

theorem G47_5_interval :
    ((((41393239/867610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 5) ∧
    (baezDuarteGramEntry 47 5 ≤ (((41566761/867610000) : ℚ) : ℝ)) := by
  rw [G47_5_formula]
  exact vasyuninBEntry_5_47_eval

def interval_47_5 : NamedVasyuninInterval :=
{
  h := 47
  k := 5
  lower := (41393239/867610000)
  upper := (41566761/867610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_5_interval
}

theorem G47_6_formula : baezDuarteGramEntry 47 6 = vasyuninBEntry 6 47 := by
  rw [baezDuarteGramEntry_symm 47 6]
  exact G6_47_formula

theorem G47_6_interval :
    ((((4534111/98890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 6) ∧
    (baezDuarteGramEntry 47 6 ≤ (((4553889/98890000) : ℚ) : ℝ)) := by
  rw [G47_6_formula]
  exact vasyuninBEntry_6_47_eval

def interval_47_6 : NamedVasyuninInterval :=
{
  h := 47
  k := 6
  lower := (4534111/98890000)
  upper := (4553889/98890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_6_interval
}

theorem G47_7_formula : baezDuarteGramEntry 47 7 = vasyuninBEntry 7 47 := by
  rw [baezDuarteGramEntry_symm 47 7]
  exact G7_47_formula

theorem G47_7_interval :
    ((((14417323/326770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 7) ∧
    (baezDuarteGramEntry 47 7 ≤ (((14482677/326770000) : ℚ) : ℝ)) := by
  rw [G47_7_formula]
  exact vasyuninBEntry_7_47_eval

def interval_47_7 : NamedVasyuninInterval :=
{
  h := 47
  k := 7
  lower := (14417323/326770000)
  upper := (14482677/326770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_7_interval
}

theorem G47_8_formula : baezDuarteGramEntry 47 8 = vasyuninBEntry 8 47 := by
  rw [baezDuarteGramEntry_symm 47 8]
  exact G8_47_formula

theorem G47_8_interval :
    ((((571167/13330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 8) ∧
    (baezDuarteGramEntry 47 8 ≤ (((573833/13330000) : ℚ) : ℝ)) := by
  rw [G47_8_formula]
  exact vasyuninBEntry_8_47_eval

def interval_47_8 : NamedVasyuninInterval :=
{
  h := 47
  k := 8
  lower := (571167/13330000)
  upper := (573833/13330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_8_interval
}

theorem G47_9_formula : baezDuarteGramEntry 47 9 = vasyuninBEntry 9 47 := by
  rw [baezDuarteGramEntry_symm 47 9]
  exact G9_47_formula

theorem G47_9_interval :
    ((((728993/17570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 9) ∧
    (baezDuarteGramEntry 47 9 ≤ (((732507/17570000) : ℚ) : ℝ)) := by
  rw [G47_9_formula]
  exact vasyuninBEntry_9_47_eval

def interval_47_9 : NamedVasyuninInterval :=
{
  h := 47
  k := 9
  lower := (728993/17570000)
  upper := (732507/17570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_9_interval
}

theorem G47_10_formula : baezDuarteGramEntry 47 10 = vasyuninBEntry 10 47 := by
  rw [baezDuarteGramEntry_symm 47 10]
  exact G10_47_formula

theorem G47_10_interval :
    ((((39142817/971830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 10) ∧
    (baezDuarteGramEntry 47 10 ≤ (((39337183/971830000) : ℚ) : ℝ)) := by
  rw [G47_10_formula]
  exact vasyuninBEntry_10_47_eval

def interval_47_10 : NamedVasyuninInterval :=
{
  h := 47
  k := 10
  lower := (39142817/971830000)
  upper := (39337183/971830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_10_interval
}

theorem G47_11_formula : baezDuarteGramEntry 47 11 = vasyuninBEntry 11 47 := by
  rw [baezDuarteGramEntry_symm 47 11]
  exact G11_47_formula

theorem G47_11_interval :
    ((((23689717/602830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 11) ∧
    (baezDuarteGramEntry 47 11 ≤ (((23810283/602830000) : ℚ) : ℝ)) := by
  rw [G47_11_formula]
  exact vasyuninBEntry_11_47_eval

def interval_47_11 : NamedVasyuninInterval :=
{
  h := 47
  k := 11
  lower := (23689717/602830000)
  upper := (23810283/602830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_11_interval
}

theorem G47_12_formula : baezDuarteGramEntry 47 12 = vasyuninBEntry 12 47 := by
  rw [baezDuarteGramEntry_symm 47 12]
  exact G12_47_formula

theorem G47_12_interval :
    ((((35647851/921490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 12) ∧
    (baezDuarteGramEntry 47 12 ≤ (((35832149/921490000) : ℚ) : ℝ)) := by
  rw [G47_12_formula]
  exact vasyuninBEntry_12_47_eval

def interval_47_12 : NamedVasyuninInterval :=
{
  h := 47
  k := 12
  lower := (35647851/921490000)
  upper := (35832149/921490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_12_interval
}

theorem G47_13_formula : baezDuarteGramEntry 47 13 = vasyuninBEntry 13 47 := by
  rw [baezDuarteGramEntry_symm 47 13]
  exact G13_47_formula

theorem G47_13_interval :
    ((((16052083/429170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 13) ∧
    (baezDuarteGramEntry 47 13 ≤ (((16137917/429170000) : ℚ) : ℝ)) := by
  rw [G47_13_formula]
  exact vasyuninBEntry_13_47_eval

def interval_47_13 : NamedVasyuninInterval :=
{
  h := 47
  k := 13
  lower := (16052083/429170000)
  upper := (16137917/429170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_13_interval
}

theorem G47_14_formula : baezDuarteGramEntry 47 14 = vasyuninBEntry 14 47 := by
  rw [baezDuarteGramEntry_symm 47 14]
  exact G14_47_formula

theorem G47_14_interval :
    ((((2553033/69670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 14) ∧
    (baezDuarteGramEntry 47 14 ≤ (((2566967/69670000) : ℚ) : ℝ)) := by
  rw [G47_14_formula]
  exact vasyuninBEntry_14_47_eval

def interval_47_14 : NamedVasyuninInterval :=
{
  h := 47
  k := 14
  lower := (2553033/69670000)
  upper := (2566967/69670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_14_interval
}

theorem G47_15_formula : baezDuarteGramEntry 47 15 = vasyuninBEntry 15 47 := by
  rw [baezDuarteGramEntry_symm 47 15]
  exact G15_47_formula

theorem G47_15_interval :
    ((((12495517/344830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 15) ∧
    (baezDuarteGramEntry 47 15 ≤ (((12564483/344830000) : ℚ) : ℝ)) := by
  rw [G47_15_formula]
  exact vasyuninBEntry_15_47_eval

def interval_47_15 : NamedVasyuninInterval :=
{
  h := 47
  k := 15
  lower := (12495517/344830000)
  upper := (12564483/344830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_15_interval
}

theorem G47_16_formula : baezDuarteGramEntry 47 16 = vasyuninBEntry 16 47 := by
  rw [baezDuarteGramEntry_symm 47 16]
  exact G16_47_formula

theorem G47_16_interval :
    ((((9159413/255870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 16) ∧
    (baezDuarteGramEntry 47 16 ≤ (((9210587/255870000) : ℚ) : ℝ)) := by
  rw [G47_16_formula]
  exact vasyuninBEntry_16_47_eval

def interval_47_16 : NamedVasyuninInterval :=
{
  h := 47
  k := 16
  lower := (9159413/255870000)
  upper := (9210587/255870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_16_interval
}

theorem G47_17_formula : baezDuarteGramEntry 47 17 = vasyuninBEntry 17 47 := by
  rw [baezDuarteGramEntry_symm 47 17]
  exact G17_47_formula

theorem G47_17_interval :
    ((((125597/3630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 17) ∧
    (baezDuarteGramEntry 47 17 ≤ (((126323/3630000) : ℚ) : ℝ)) := by
  rw [G47_17_formula]
  exact vasyuninBEntry_17_47_eval

def interval_47_17 : NamedVasyuninInterval :=
{
  h := 47
  k := 17
  lower := (125597/3630000)
  upper := (126323/3630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_17_interval
}

theorem G47_18_formula : baezDuarteGramEntry 47 18 = vasyuninBEntry 18 47 := by
  rw [baezDuarteGramEntry_symm 47 18]
  exact G18_47_formula

theorem G47_18_interval :
    ((((25624307/756930000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 18) ∧
    (baezDuarteGramEntry 47 18 ≤ (((25775693/756930000) : ℚ) : ℝ)) := by
  rw [G47_18_formula]
  exact vasyuninBEntry_18_47_eval

def interval_47_18 : NamedVasyuninInterval :=
{
  h := 47
  k := 18
  lower := (25624307/756930000)
  upper := (25775693/756930000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_18_interval
}

theorem G47_19_formula : baezDuarteGramEntry 47 19 = vasyuninBEntry 19 47 := by
  rw [baezDuarteGramEntry_symm 47 19]
  exact G19_47_formula

theorem G47_19_interval :
    ((((107677/3230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 19) ∧
    (baezDuarteGramEntry 47 19 ≤ (((108323/3230000) : ℚ) : ℝ)) := by
  rw [G47_19_formula]
  exact vasyuninBEntry_19_47_eval

def interval_47_19 : NamedVasyuninInterval :=
{
  h := 47
  k := 19
  lower := (107677/3230000)
  upper := (108323/3230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_19_interval
}

theorem G47_20_formula : baezDuarteGramEntry 47 20 = vasyuninBEntry 20 47 := by
  rw [baezDuarteGramEntry_symm 47 20]
  exact G20_47_formula

theorem G47_20_interval :
    ((((12686317/386830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 20) ∧
    (baezDuarteGramEntry 47 20 ≤ (((12763683/386830000) : ℚ) : ℝ)) := by
  rw [G47_20_formula]
  exact vasyuninBEntry_20_47_eval

def interval_47_20 : NamedVasyuninInterval :=
{
  h := 47
  k := 20
  lower := (12686317/386830000)
  upper := (12763683/386830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_20_interval
}

theorem G47_21_formula : baezDuarteGramEntry 47 21 = vasyuninBEntry 21 47 := by
  rw [baezDuarteGramEntry_symm 47 21]
  exact G21_47_formula

theorem G47_21_interval :
    ((((1186341/36590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 21) ∧
    (baezDuarteGramEntry 47 21 ≤ (((1193659/36590000) : ℚ) : ℝ)) := by
  rw [G47_21_formula]
  exact vasyuninBEntry_21_47_eval

def interval_47_21 : NamedVasyuninInterval :=
{
  h := 47
  k := 21
  lower := (1186341/36590000)
  upper := (1193659/36590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_21_interval
}

theorem G47_22_formula : baezDuarteGramEntry 47 22 = vasyuninBEntry 22 47 := by
  rw [baezDuarteGramEntry_symm 47 22]
  exact G22_47_formula

theorem G47_22_interval :
    ((((9779657/303430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 22) ∧
    (baezDuarteGramEntry 47 22 ≤ (((9840343/303430000) : ℚ) : ℝ)) := by
  rw [G47_22_formula]
  exact vasyuninBEntry_22_47_eval

def interval_47_22 : NamedVasyuninInterval :=
{
  h := 47
  k := 22
  lower := (9779657/303430000)
  upper := (9840343/303430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_22_interval
}

theorem G47_23_formula : baezDuarteGramEntry 47 23 = vasyuninBEntry 23 47 := by
  rw [baezDuarteGramEntry_symm 47 23]
  exact G23_47_formula

theorem G47_23_interval :
    ((((13916977/430230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 23) ∧
    (baezDuarteGramEntry 47 23 ≤ (((14003023/430230000) : ℚ) : ℝ)) := by
  rw [G47_23_formula]
  exact vasyuninBEntry_23_47_eval

def interval_47_23 : NamedVasyuninInterval :=
{
  h := 47
  k := 23
  lower := (13916977/430230000)
  upper := (14003023/430230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_23_interval
}

theorem G47_24_formula : baezDuarteGramEntry 47 24 = vasyuninBEntry 24 47 := by
  rw [baezDuarteGramEntry_symm 47 24]
  exact G24_47_formula

theorem G47_24_interval :
    ((((1207709/37910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 24) ∧
    (baezDuarteGramEntry 47 24 ≤ (((1215291/37910000) : ℚ) : ℝ)) := by
  rw [G47_24_formula]
  exact vasyuninBEntry_24_47_eval

def interval_47_24 : NamedVasyuninInterval :=
{
  h := 47
  k := 24
  lower := (1207709/37910000)
  upper := (1215291/37910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_24_interval
}

theorem G47_25_formula : baezDuarteGramEntry 47 25 = vasyuninBEntry 25 47 := by
  rw [baezDuarteGramEntry_symm 47 25]
  exact G25_47_formula

theorem G47_25_interval :
    ((((28846369/936310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 25) ∧
    (baezDuarteGramEntry 47 25 ≤ (((29033631/936310000) : ℚ) : ℝ)) := by
  rw [G47_25_formula]
  exact vasyuninBEntry_25_47_eval

def interval_47_25 : NamedVasyuninInterval :=
{
  h := 47
  k := 25
  lower := (28846369/936310000)
  upper := (29033631/936310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_25_interval
}

theorem G47_26_formula : baezDuarteGramEntry 47 26 = vasyuninBEntry 26 47 := by
  rw [baezDuarteGramEntry_symm 47 26]
  exact G26_47_formula

theorem G47_26_interval :
    ((((838811/27890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 26) ∧
    (baezDuarteGramEntry 47 26 ≤ (((844389/27890000) : ℚ) : ℝ)) := by
  rw [G47_26_formula]
  exact vasyuninBEntry_26_47_eval

def interval_47_26 : NamedVasyuninInterval :=
{
  h := 47
  k := 26
  lower := (838811/27890000)
  upper := (844389/27890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_26_interval
}

theorem G47_27_formula : baezDuarteGramEntry 47 27 = vasyuninBEntry 27 47 := by
  rw [baezDuarteGramEntry_symm 47 27]
  exact G27_47_formula

theorem G47_27_interval :
    ((((7153253/242470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 27) ∧
    (baezDuarteGramEntry 47 27 ≤ (((7201747/242470000) : ℚ) : ℝ)) := by
  rw [G47_27_formula]
  exact vasyuninBEntry_27_47_eval

def interval_47_27 : NamedVasyuninInterval :=
{
  h := 47
  k := 27
  lower := (7153253/242470000)
  upper := (7201747/242470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_27_interval
}

theorem G47_28_formula : baezDuarteGramEntry 47 28 = vasyuninBEntry 28 47 := by
  rw [baezDuarteGramEntry_symm 47 28]
  exact G28_47_formula

theorem G47_28_interval :
    ((((4786019/164810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 28) ∧
    (baezDuarteGramEntry 47 28 ≤ (((4818981/164810000) : ℚ) : ℝ)) := by
  rw [G47_28_formula]
  exact vasyuninBEntry_28_47_eval

def interval_47_28 : NamedVasyuninInterval :=
{
  h := 47
  k := 28
  lower := (4786019/164810000)
  upper := (4818981/164810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_28_interval
}

theorem G47_29_formula : baezDuarteGramEntry 47 29 = vasyuninBEntry 29 47 := by
  rw [baezDuarteGramEntry_symm 47 29]
  exact G29_47_formula

theorem G47_29_interval :
    ((((1118089/39110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 29) ∧
    (baezDuarteGramEntry 47 29 ≤ (((1125911/39110000) : ℚ) : ℝ)) := by
  rw [G47_29_formula]
  exact vasyuninBEntry_29_47_eval

def interval_47_29 : NamedVasyuninInterval :=
{
  h := 47
  k := 29
  lower := (1118089/39110000)
  upper := (1125911/39110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_29_interval
}

theorem G47_30_formula : baezDuarteGramEntry 47 30 = vasyuninBEntry 30 47 := by
  rw [baezDuarteGramEntry_symm 47 30]
  exact G30_47_formula

theorem G47_30_interval :
    ((((28090519/994810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 30) ∧
    (baezDuarteGramEntry 47 30 ≤ (((28289481/994810000) : ℚ) : ℝ)) := by
  rw [G47_30_formula]
  exact vasyuninBEntry_30_47_eval

def interval_47_30 : NamedVasyuninInterval :=
{
  h := 47
  k := 30
  lower := (28090519/994810000)
  upper := (28289481/994810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_30_interval
}

theorem G47_31_formula : baezDuarteGramEntry 47 31 = vasyuninBEntry 31 47 := by
  rw [baezDuarteGramEntry_symm 47 31]
  exact G31_47_formula

theorem G47_31_interval :
    ((((27491899/981010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 31) ∧
    (baezDuarteGramEntry 47 31 ≤ (((27688101/981010000) : ℚ) : ℝ)) := by
  rw [G47_31_formula]
  exact vasyuninBEntry_31_47_eval

def interval_47_31 : NamedVasyuninInterval :=
{
  h := 47
  k := 31
  lower := (27491899/981010000)
  upper := (27688101/981010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_31_interval
}

theorem G47_32_formula : baezDuarteGramEntry 47 32 = vasyuninBEntry 32 47 := by
  rw [baezDuarteGramEntry_symm 47 32]
  exact G32_47_formula

theorem G47_32_interval :
    ((((20605429/745710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 32) ∧
    (baezDuarteGramEntry 47 32 ≤ (((20754571/745710000) : ℚ) : ℝ)) := by
  rw [G47_32_formula]
  exact vasyuninBEntry_32_47_eval

def interval_47_32 : NamedVasyuninInterval :=
{
  h := 47
  k := 32
  lower := (20605429/745710000)
  upper := (20754571/745710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_32_interval
}

theorem G47_33_formula : baezDuarteGramEntry 47 33 = vasyuninBEntry 33 47 := by
  rw [baezDuarteGramEntry_symm 47 33]
  exact G33_47_formula

theorem G47_33_interval :
    ((((1342573/49270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 33) ∧
    (baezDuarteGramEntry 47 33 ≤ (((1352427/49270000) : ℚ) : ℝ)) := by
  rw [G47_33_formula]
  exact vasyuninBEntry_33_47_eval

def interval_47_33 : NamedVasyuninInterval :=
{
  h := 47
  k := 33
  lower := (1342573/49270000)
  upper := (1352427/49270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_33_interval
}

theorem G47_34_formula : baezDuarteGramEntry 47 34 = vasyuninBEntry 34 47 := by
  rw [baezDuarteGramEntry_symm 47 34]
  exact G34_47_formula

theorem G47_34_interval :
    ((((23990999/890010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 34) ∧
    (baezDuarteGramEntry 47 34 ≤ (((24169001/890010000) : ℚ) : ℝ)) := by
  rw [G47_34_formula]
  exact vasyuninBEntry_34_47_eval

def interval_47_34 : NamedVasyuninInterval :=
{
  h := 47
  k := 34
  lower := (23990999/890010000)
  upper := (24169001/890010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_34_interval
}

theorem G47_35_formula : baezDuarteGramEntry 47 35 = vasyuninBEntry 35 47 := by
  rw [baezDuarteGramEntry_symm 47 35]
  exact G35_47_formula

theorem G47_35_interval :
    ((((200351/7490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 35) ∧
    (baezDuarteGramEntry 47 35 ≤ (((201849/7490000) : ℚ) : ℝ)) := by
  rw [G47_35_formula]
  exact vasyuninBEntry_35_47_eval

def interval_47_35 : NamedVasyuninInterval :=
{
  h := 47
  k := 35
  lower := (200351/7490000)
  upper := (201849/7490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_35_interval
}

theorem G47_36_formula : baezDuarteGramEntry 47 36 = vasyuninBEntry 36 47 := by
  rw [baezDuarteGramEntry_symm 47 36]
  exact G36_47_formula

theorem G47_36_interval :
    ((((20582293/777070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 36) ∧
    (baezDuarteGramEntry 47 36 ≤ (((20737707/777070000) : ℚ) : ℝ)) := by
  rw [G47_36_formula]
  exact vasyuninBEntry_36_47_eval

def interval_47_36 : NamedVasyuninInterval :=
{
  h := 47
  k := 36
  lower := (20582293/777070000)
  upper := (20737707/777070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_36_interval
}

theorem G47_37_formula : baezDuarteGramEntry 47 37 = vasyuninBEntry 37 47 := by
  rw [baezDuarteGramEntry_symm 47 37]
  exact G37_47_formula

theorem G47_37_interval :
    ((((24307501/924990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 37) ∧
    (baezDuarteGramEntry 47 37 ≤ (((24492499/924990000) : ℚ) : ℝ)) := by
  rw [G47_37_formula]
  exact vasyuninBEntry_37_47_eval

def interval_47_37 : NamedVasyuninInterval :=
{
  h := 47
  k := 37
  lower := (24307501/924990000)
  upper := (24492499/924990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_37_interval
}

theorem G47_38_formula : baezDuarteGramEntry 47 38 = vasyuninBEntry 38 47 := by
  rw [baezDuarteGramEntry_symm 47 38]
  exact G38_47_formula

theorem G47_38_interval :
    ((((25791229/987710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 38) ∧
    (baezDuarteGramEntry 47 38 ≤ (((25988771/987710000) : ℚ) : ℝ)) := by
  rw [G47_38_formula]
  exact vasyuninBEntry_38_47_eval

def interval_47_38 : NamedVasyuninInterval :=
{
  h := 47
  k := 38
  lower := (25791229/987710000)
  upper := (25988771/987710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_38_interval
}

theorem G47_39_formula : baezDuarteGramEntry 47 39 = vasyuninBEntry 39 47 := by
  rw [baezDuarteGramEntry_symm 47 39]
  exact G39_47_formula

theorem G47_39_interval :
    ((((3705731/142690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 39) ∧
    (baezDuarteGramEntry 47 39 ≤ (((3734269/142690000) : ℚ) : ℝ)) := by
  rw [G47_39_formula]
  exact vasyuninBEntry_39_47_eval

def interval_47_39 : NamedVasyuninInterval :=
{
  h := 47
  k := 39
  lower := (3705731/142690000)
  upper := (3734269/142690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_39_interval
}

theorem G47_40_formula : baezDuarteGramEntry 47 40 = vasyuninBEntry 40 47 := by
  rw [baezDuarteGramEntry_symm 47 40]
  exact G40_47_formula

theorem G47_40_interval :
    ((((196739/7610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 40) ∧
    (baezDuarteGramEntry 47 40 ≤ (((198261/7610000) : ℚ) : ℝ)) := by
  rw [G47_40_formula]
  exact vasyuninBEntry_40_47_eval

def interval_47_40 : NamedVasyuninInterval :=
{
  h := 47
  k := 40
  lower := (196739/7610000)
  upper := (198261/7610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_40_interval
}

theorem G47_41_formula : baezDuarteGramEntry 47 41 = vasyuninBEntry 41 47 := by
  rw [baezDuarteGramEntry_symm 47 41]
  exact G41_47_formula

theorem G47_41_interval :
    ((((22682009/879910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 41) ∧
    (baezDuarteGramEntry 47 41 ≤ (((22857991/879910000) : ℚ) : ℝ)) := by
  rw [G47_41_formula]
  exact vasyuninBEntry_41_47_eval

def interval_47_41 : NamedVasyuninInterval :=
{
  h := 47
  k := 41
  lower := (22682009/879910000)
  upper := (22857991/879910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_41_interval
}

theorem G47_42_formula : baezDuarteGramEntry 47 42 = vasyuninBEntry 42 47 := by
  rw [baezDuarteGramEntry_symm 47 42]
  exact G42_47_formula

theorem G47_42_interval :
    ((((4861113/188870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 42) ∧
    (baezDuarteGramEntry 47 42 ≤ (((4898887/188870000) : ℚ) : ℝ)) := by
  rw [G47_42_formula]
  exact vasyuninBEntry_42_47_eval

def interval_47_42 : NamedVasyuninInterval :=
{
  h := 47
  k := 42
  lower := (4861113/188870000)
  upper := (4898887/188870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_42_interval
}

theorem G47_43_formula : baezDuarteGramEntry 47 43 = vasyuninBEntry 43 47 := by
  rw [baezDuarteGramEntry_symm 47 43]
  exact G43_47_formula

theorem G47_43_interval :
    ((((1096989/42610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 43) ∧
    (baezDuarteGramEntry 47 43 ≤ (((1105511/42610000) : ℚ) : ℝ)) := by
  rw [G47_43_formula]
  exact vasyuninBEntry_43_47_eval

def interval_47_43 : NamedVasyuninInterval :=
{
  h := 47
  k := 43
  lower := (1096989/42610000)
  upper := (1105511/42610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_43_interval
}

theorem G47_44_formula : baezDuarteGramEntry 47 44 = vasyuninBEntry 44 47 := by
  rw [baezDuarteGramEntry_symm 47 44]
  exact G44_47_formula

theorem G47_44_interval :
    ((((16187273/627270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 44) ∧
    (baezDuarteGramEntry 47 44 ≤ (((16312727/627270000) : ℚ) : ℝ)) := by
  rw [G47_44_formula]
  exact vasyuninBEntry_44_47_eval

def interval_47_44 : NamedVasyuninInterval :=
{
  h := 47
  k := 44
  lower := (16187273/627270000)
  upper := (16312727/627270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_44_interval
}

theorem G47_45_formula : baezDuarteGramEntry 47 45 = vasyuninBEntry 45 47 := by
  rw [baezDuarteGramEntry_symm 47 45]
  exact G45_47_formula

theorem G47_45_interval :
    ((((6186151/238490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 45) ∧
    (baezDuarteGramEntry 47 45 ≤ (((6233849/238490000) : ℚ) : ℝ)) := by
  rw [G47_45_formula]
  exact vasyuninBEntry_45_47_eval

def interval_47_45 : NamedVasyuninInterval :=
{
  h := 47
  k := 45
  lower := (6186151/238490000)
  upper := (6233849/238490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_45_interval
}

theorem G47_46_formula : baezDuarteGramEntry 47 46 = vasyuninBEntry 46 47 := by
  rw [baezDuarteGramEntry_symm 47 46]
  exact G46_47_formula

theorem G47_46_interval :
    ((((5531373/211270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 46) ∧
    (baezDuarteGramEntry 47 46 ≤ (((5573627/211270000) : ℚ) : ℝ)) := by
  rw [G47_46_formula]
  exact vasyuninBEntry_46_47_eval

def interval_47_46 : NamedVasyuninInterval :=
{
  h := 47
  k := 46
  lower := (5531373/211270000)
  upper := (5573627/211270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_46_interval
}

theorem G47_47_formula_eq : baezDuarteGramEntry 47 47 = (1 / (47 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 47 := by norm_num
  rw [baez_duarte_diagonal_scaling 47 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G47_47_log_gamma_interval :
  ((((1876727/70230000) : ℚ) : ℝ) ≤ (1 / (47 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (47 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((1890773/70230000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 47 (by norm_num)
  constructor
  · have : ((((1876727/70230000) : ℚ) : ℝ) ≤ (1 / (47 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (47 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((1890773/70230000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G47_47_interval : ((((1876727/70230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 47) ∧ (baezDuarteGramEntry 47 47 ≤ (((1890773/70230000) : ℚ) : ℝ)) := by
  rw [G47_47_formula_eq]
  exact G47_47_log_gamma_interval

def interval_47_47 : NamedVasyuninInterval :=
{
  h := 47
  k := 47
  lower := (1876727/70230000)
  upper := (1890773/70230000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G47_47_interval
}

theorem G47_48_formula : baezDuarteGramEntry 47 48 = vasyuninBEntry 47 48 := vasyuninBEntry_correct_axiom 47 48

theorem vasyuninBEntry_47_48_eval :
    ((((4041737/157630000) : ℚ) : ℝ) ≤ vasyuninBEntry 47 48) ∧
    (vasyuninBEntry 47 48 ≤ (((4073263/157630000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4748_formula_bound
  constructor <;> linarith

theorem G47_48_interval :
    ((((4041737/157630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 48) ∧
    (baezDuarteGramEntry 47 48 ≤ (((4073263/157630000) : ℚ) : ℝ)) := by
  rw [G47_48_formula]
  exact vasyuninBEntry_47_48_eval

def interval_47_48 : NamedVasyuninInterval :=
{
  h := 47
  k := 48
  lower := (4041737/157630000)
  upper := (4073263/157630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_48_interval
}

theorem G47_49_formula : baezDuarteGramEntry 47 49 = vasyuninBEntry 47 49 := vasyuninBEntry_correct_axiom 47 49

theorem vasyuninBEntry_47_49_eval :
    ((((23774483/955170000) : ℚ) : ℝ) ≤ vasyuninBEntry 47 49) ∧
    (vasyuninBEntry 47 49 ≤ (((23965517/955170000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4749_formula_bound
  constructor <;> linarith

theorem G47_49_interval :
    ((((23774483/955170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 49) ∧
    (baezDuarteGramEntry 47 49 ≤ (((23965517/955170000) : ℚ) : ℝ)) := by
  rw [G47_49_formula]
  exact vasyuninBEntry_47_49_eval

def interval_47_49 : NamedVasyuninInterval :=
{
  h := 47
  k := 49
  lower := (23774483/955170000)
  upper := (23965517/955170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_49_interval
}

theorem G47_50_formula : baezDuarteGramEntry 47 50 = vasyuninBEntry 47 50 := vasyuninBEntry_correct_axiom 47 50

theorem vasyuninBEntry_47_50_eval :
    ((((23313933/960670000) : ℚ) : ℝ) ≤ vasyuninBEntry 47 50) ∧
    (vasyuninBEntry 47 50 ≤ (((23506067/960670000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4750_formula_bound
  constructor <;> linarith

theorem G47_50_interval :
    ((((23313933/960670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 47 50) ∧
    (baezDuarteGramEntry 47 50 ≤ (((23506067/960670000) : ℚ) : ℝ)) := by
  rw [G47_50_formula]
  exact vasyuninBEntry_47_50_eval

def interval_47_50 : NamedVasyuninInterval :=
{
  h := 47
  k := 50
  lower := (23313933/960670000)
  upper := (23506067/960670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G47_50_interval
}

theorem G48_1_formula : baezDuarteGramEntry 48 1 = vasyuninBEntry 1 48 := by
  rw [baezDuarteGramEntry_symm 48 1]
  exact G1_48_formula

theorem G48_1_interval :
    ((((17622393/276070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 1) ∧
    (baezDuarteGramEntry 48 1 ≤ (((17677607/276070000) : ℚ) : ℝ)) := by
  rw [G48_1_formula]
  exact vasyuninBEntry_1_48_eval

def interval_48_1 : NamedVasyuninInterval :=
{
  h := 48
  k := 1
  lower := (17622393/276070000)
  upper := (17677607/276070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_1_interval
}

theorem G48_2_formula : baezDuarteGramEntry 48 2 = vasyuninBEntry 2 48 := by
  rw [baezDuarteGramEntry_symm 48 2]
  exact G2_48_formula

theorem G48_2_interval :
    ((((51469181/908190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 2) ∧
    (baezDuarteGramEntry 48 2 ≤ (((51650819/908190000) : ℚ) : ℝ)) := by
  rw [G48_2_formula]
  exact vasyuninBEntry_2_48_eval

def interval_48_2 : NamedVasyuninInterval :=
{
  h := 48
  k := 2
  lower := (51469181/908190000)
  upper := (51650819/908190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_2_interval
}

theorem G48_3_formula : baezDuarteGramEntry 48 3 = vasyuninBEntry 3 48 := by
  rw [baezDuarteGramEntry_symm 48 3]
  exact G3_48_formula

theorem G48_3_interval :
    ((((44784709/852910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 3) ∧
    (baezDuarteGramEntry 48 3 ≤ (((44955291/852910000) : ℚ) : ℝ)) := by
  rw [G48_3_formula]
  exact vasyuninBEntry_3_48_eval

def interval_48_3 : NamedVasyuninInterval :=
{
  h := 48
  k := 3
  lower := (44784709/852910000)
  upper := (44955291/852910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_3_interval
}

theorem G48_4_formula : baezDuarteGramEntry 48 4 = vasyuninBEntry 4 48 := by
  rw [baezDuarteGramEntry_symm 48 4]
  exact G4_48_formula

theorem G48_4_interval :
    ((((11898497/240030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 4) ∧
    (baezDuarteGramEntry 48 4 ≤ (((11946503/240030000) : ℚ) : ℝ)) := by
  rw [G48_4_formula]
  exact vasyuninBEntry_4_48_eval

def interval_48_4 : NamedVasyuninInterval :=
{
  h := 48
  k := 4
  lower := (11898497/240030000)
  upper := (11946503/240030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_4_interval
}

theorem G48_5_formula : baezDuarteGramEntry 48 5 = vasyuninBEntry 5 48 := by
  rw [baezDuarteGramEntry_symm 48 5]
  exact G5_48_formula

theorem G48_5_interval :
    ((((2906931/61940000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 5) ∧
    (baezDuarteGramEntry 48 5 ≤ (((2919319/61940000) : ℚ) : ℝ)) := by
  rw [G48_5_formula]
  exact vasyuninBEntry_5_48_eval

def interval_48_5 : NamedVasyuninInterval :=
{
  h := 48
  k := 5
  lower := (2906931/61940000)
  upper := (2919319/61940000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_5_interval
}

theorem G48_6_formula : baezDuarteGramEntry 48 6 = vasyuninBEntry 6 48 := by
  rw [baezDuarteGramEntry_symm 48 6]
  exact G6_48_formula

theorem G48_6_interval :
    ((((42456619/933810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 6) ∧
    (baezDuarteGramEntry 48 6 ≤ (((42643381/933810000) : ℚ) : ℝ)) := by
  rw [G48_6_formula]
  exact vasyuninBEntry_6_48_eval

def interval_48_6 : NamedVasyuninInterval :=
{
  h := 48
  k := 6
  lower := (42456619/933810000)
  upper := (42643381/933810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_6_interval
}

theorem G48_7_formula : baezDuarteGramEntry 48 7 = vasyuninBEntry 7 48 := by
  rw [baezDuarteGramEntry_symm 48 7]
  exact G7_48_formula

theorem G48_7_interval :
    ((((21395851/491490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 7) ∧
    (baezDuarteGramEntry 48 7 ≤ (((21494149/491490000) : ℚ) : ℝ)) := by
  rw [G48_7_formula]
  exact vasyuninBEntry_7_48_eval

def interval_48_7 : NamedVasyuninInterval :=
{
  h := 48
  k := 7
  lower := (21395851/491490000)
  upper := (21494149/491490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_7_interval
}

theorem G48_8_formula : baezDuarteGramEntry 48 8 = vasyuninBEntry 8 48 := by
  rw [baezDuarteGramEntry_symm 48 8]
  exact G8_48_formula

theorem G48_8_interval :
    ((((35536557/834430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 8) ∧
    (baezDuarteGramEntry 48 8 ≤ (((35703443/834430000) : ℚ) : ℝ)) := by
  rw [G48_8_formula]
  exact vasyuninBEntry_8_48_eval

def interval_48_8 : NamedVasyuninInterval :=
{
  h := 48
  k := 8
  lower := (35536557/834430000)
  upper := (35703443/834430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_8_interval
}

theorem G48_9_formula : baezDuarteGramEntry 48 9 = vasyuninBEntry 9 48 := by
  rw [baezDuarteGramEntry_symm 48 9]
  exact G9_48_formula

theorem G48_9_interval :
    ((((19761559/484410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 9) ∧
    (baezDuarteGramEntry 48 9 ≤ (((19858441/484410000) : ℚ) : ℝ)) := by
  rw [G48_9_formula]
  exact vasyuninBEntry_9_48_eval

def interval_48_9 : NamedVasyuninInterval :=
{
  h := 48
  k := 9
  lower := (19761559/484410000)
  upper := (19858441/484410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_9_interval
}

theorem G48_10_formula : baezDuarteGramEntry 48 10 = vasyuninBEntry 10 48 := by
  rw [baezDuarteGramEntry_symm 48 10]
  exact G10_48_formula

theorem G48_10_interval :
    ((((790511/19890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 10) ∧
    (baezDuarteGramEntry 48 10 ≤ (((794489/19890000) : ℚ) : ℝ)) := by
  rw [G48_10_formula]
  exact vasyuninBEntry_10_48_eval

def interval_48_10 : NamedVasyuninInterval :=
{
  h := 48
  k := 10
  lower := (790511/19890000)
  upper := (794489/19890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_10_interval
}

theorem G48_11_formula : baezDuarteGramEntry 48 11 = vasyuninBEntry 11 48 := by
  rw [baezDuarteGramEntry_symm 48 11]
  exact G11_48_formula

theorem G48_11_interval :
    ((((13265673/343270000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 11) ∧
    (baezDuarteGramEntry 48 11 ≤ (((13334327/343270000) : ℚ) : ℝ)) := by
  rw [G48_11_formula]
  exact vasyuninBEntry_11_48_eval

def interval_48_11 : NamedVasyuninInterval :=
{
  h := 48
  k := 11
  lower := (13265673/343270000)
  upper := (13334327/343270000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_11_interval
}

theorem G48_12_formula : baezDuarteGramEntry 48 12 = vasyuninBEntry 12 48 := by
  rw [baezDuarteGramEntry_symm 48 12]
  exact G12_48_formula

theorem G48_12_interval :
    ((((12627287/327130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 12) ∧
    (baezDuarteGramEntry 48 12 ≤ (((12692713/327130000) : ℚ) : ℝ)) := by
  rw [G48_12_formula]
  exact vasyuninBEntry_12_48_eval

def interval_48_12 : NamedVasyuninInterval :=
{
  h := 48
  k := 12
  lower := (12627287/327130000)
  upper := (12692713/327130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_12_interval
}

theorem G48_13_formula : baezDuarteGramEntry 48 13 = vasyuninBEntry 13 48 := by
  rw [baezDuarteGramEntry_symm 48 13]
  exact G13_48_formula

theorem G48_13_interval :
    ((((239351/6490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 13) ∧
    (baezDuarteGramEntry 48 13 ≤ (((240649/6490000) : ℚ) : ℝ)) := by
  rw [G48_13_formula]
  exact vasyuninBEntry_13_48_eval

def interval_48_13 : NamedVasyuninInterval :=
{
  h := 48
  k := 13
  lower := (239351/6490000)
  upper := (240649/6490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_13_interval
}

theorem G48_14_formula : baezDuarteGramEntry 48 14 = vasyuninBEntry 14 48 := by
  rw [baezDuarteGramEntry_symm 48 14]
  exact G14_48_formula

theorem G48_14_interval :
    ((((3970993/110070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 14) ∧
    (baezDuarteGramEntry 48 14 ≤ (((3993007/110070000) : ℚ) : ℝ)) := by
  rw [G48_14_formula]
  exact vasyuninBEntry_14_48_eval

def interval_48_14 : NamedVasyuninInterval :=
{
  h := 48
  k := 14
  lower := (3970993/110070000)
  upper := (3993007/110070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_14_interval
}

theorem G48_15_formula : baezDuarteGramEntry 48 15 = vasyuninBEntry 15 48 := by
  rw [baezDuarteGramEntry_symm 48 15]
  exact G15_48_formula

theorem G48_15_interval :
    ((((10540353/296470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 15) ∧
    (baezDuarteGramEntry 48 15 ≤ (((10599647/296470000) : ℚ) : ℝ)) := by
  rw [G48_15_formula]
  exact vasyuninBEntry_15_48_eval

def interval_48_15 : NamedVasyuninInterval :=
{
  h := 48
  k := 15
  lower := (10540353/296470000)
  upper := (10599647/296470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_15_interval
}

theorem G48_16_formula : baezDuarteGramEntry 48 16 = vasyuninBEntry 16 48 := by
  rw [baezDuarteGramEntry_symm 48 16]
  exact G16_48_formula

theorem G48_16_interval :
    ((((33626171/938290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 16) ∧
    (baezDuarteGramEntry 48 16 ≤ (((33813829/938290000) : ℚ) : ℝ)) := by
  rw [G48_16_formula]
  exact vasyuninBEntry_16_48_eval

def interval_48_16 : NamedVasyuninInterval :=
{
  h := 48
  k := 16
  lower := (33626171/938290000)
  upper := (33813829/938290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_16_interval
}

theorem G48_17_formula : baezDuarteGramEntry 48 17 = vasyuninBEntry 17 48 := by
  rw [baezDuarteGramEntry_symm 48 17]
  exact G17_48_formula

theorem G48_17_interval :
    ((((23491331/686690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 17) ∧
    (baezDuarteGramEntry 48 17 ≤ (((23628669/686690000) : ℚ) : ℝ)) := by
  rw [G48_17_formula]
  exact vasyuninBEntry_17_48_eval

def interval_48_17 : NamedVasyuninInterval :=
{
  h := 48
  k := 17
  lower := (23491331/686690000)
  upper := (23628669/686690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_17_interval
}

theorem G48_18_formula : baezDuarteGramEntry 48 18 = vasyuninBEntry 18 48 := by
  rw [baezDuarteGramEntry_symm 48 18]
  exact G18_48_formula

theorem G48_18_interval :
    ((((12128731/362690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 18) ∧
    (baezDuarteGramEntry 48 18 ≤ (((12201269/362690000) : ℚ) : ℝ)) := by
  rw [G48_18_formula]
  exact vasyuninBEntry_18_48_eval

def interval_48_18 : NamedVasyuninInterval :=
{
  h := 48
  k := 18
  lower := (12128731/362690000)
  upper := (12201269/362690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_18_interval
}

theorem G48_19_formula : baezDuarteGramEntry 48 19 = vasyuninBEntry 19 48 := by
  rw [baezDuarteGramEntry_symm 48 19]
  exact G19_48_formula

theorem G48_19_interval :
    ((((29041609/883910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 19) ∧
    (baezDuarteGramEntry 48 19 ≤ (((29218391/883910000) : ℚ) : ℝ)) := by
  rw [G48_19_formula]
  exact vasyuninBEntry_19_48_eval

def interval_48_19 : NamedVasyuninInterval :=
{
  h := 48
  k := 19
  lower := (29041609/883910000)
  upper := (29218391/883910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_19_interval
}

theorem G48_20_formula : baezDuarteGramEntry 48 20 = vasyuninBEntry 20 48 := by
  rw [baezDuarteGramEntry_symm 48 20]
  exact G20_48_formula

theorem G48_20_interval :
    ((((29717979/920210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 20) ∧
    (baezDuarteGramEntry 48 20 ≤ (((29902021/920210000) : ℚ) : ℝ)) := by
  rw [G48_20_formula]
  exact vasyuninBEntry_20_48_eval

def interval_48_20 : NamedVasyuninInterval :=
{
  h := 48
  k := 20
  lower := (29717979/920210000)
  upper := (29902021/920210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_20_interval
}

theorem G48_21_formula : baezDuarteGramEntry 48 21 = vasyuninBEntry 21 48 := by
  rw [baezDuarteGramEntry_symm 48 21]
  exact G21_48_formula

theorem G48_21_interval :
    ((((1043527/32730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 21) ∧
    (baezDuarteGramEntry 48 21 ≤ (((1050073/32730000) : ℚ) : ℝ)) := by
  rw [G48_21_formula]
  exact vasyuninBEntry_21_48_eval

def interval_48_21 : NamedVasyuninInterval :=
{
  h := 48
  k := 21
  lower := (1043527/32730000)
  upper := (1050073/32730000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_21_interval
}

theorem G48_22_formula : baezDuarteGramEntry 48 22 = vasyuninBEntry 22 48 := by
  rw [baezDuarteGramEntry_symm 48 22]
  exact G22_48_formula

theorem G48_22_interval :
    ((((13851189/438110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 22) ∧
    (baezDuarteGramEntry 48 22 ≤ (((13938811/438110000) : ℚ) : ℝ)) := by
  rw [G48_22_formula]
  exact vasyuninBEntry_22_48_eval

def interval_48_22 : NamedVasyuninInterval :=
{
  h := 48
  k := 22
  lower := (13851189/438110000)
  upper := (13938811/438110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_22_interval
}

theorem G48_23_formula : baezDuarteGramEntry 48 23 = vasyuninBEntry 23 48 := by
  rw [baezDuarteGramEntry_symm 48 23]
  exact G23_48_formula

theorem G48_23_interval :
    ((((25987663/823370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 23) ∧
    (baezDuarteGramEntry 48 23 ≤ (((26152337/823370000) : ℚ) : ℝ)) := by
  rw [G48_23_formula]
  exact vasyuninBEntry_23_48_eval

def interval_48_23 : NamedVasyuninInterval :=
{
  h := 48
  k := 23
  lower := (25987663/823370000)
  upper := (26152337/823370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_23_interval
}

theorem G48_24_formula : baezDuarteGramEntry 48 24 = vasyuninBEntry 24 48 := by
  rw [baezDuarteGramEntry_symm 48 24]
  exact G24_48_formula

theorem G48_24_interval :
    ((((7008151/218490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 24) ∧
    (baezDuarteGramEntry 48 24 ≤ (((7051849/218490000) : ℚ) : ℝ)) := by
  rw [G48_24_formula]
  exact vasyuninBEntry_24_48_eval

def interval_48_24 : NamedVasyuninInterval :=
{
  h := 48
  k := 24
  lower := (7008151/218490000)
  upper := (7051849/218490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_24_interval
}

theorem G48_25_formula : baezDuarteGramEntry 48 25 = vasyuninBEntry 25 48 := by
  rw [baezDuarteGramEntry_symm 48 25]
  exact G25_48_formula

theorem G48_25_interval :
    ((((23523231/767690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 25) ∧
    (baezDuarteGramEntry 48 25 ≤ (((23676769/767690000) : ℚ) : ℝ)) := by
  rw [G48_25_formula]
  exact vasyuninBEntry_25_48_eval

def interval_48_25 : NamedVasyuninInterval :=
{
  h := 48
  k := 25
  lower := (23523231/767690000)
  upper := (23676769/767690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_25_interval
}

theorem G48_26_formula : baezDuarteGramEntry 48 26 = vasyuninBEntry 26 48 := by
  rw [baezDuarteGramEntry_symm 48 26]
  exact G26_48_formula

theorem G48_26_interval :
    ((((27956219/937810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 26) ∧
    (baezDuarteGramEntry 48 26 ≤ (((28143781/937810000) : ℚ) : ℝ)) := by
  rw [G48_26_formula]
  exact vasyuninBEntry_26_48_eval

def interval_48_26 : NamedVasyuninInterval :=
{
  h := 48
  k := 26
  lower := (27956219/937810000)
  upper := (28143781/937810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_26_interval
}

theorem G48_27_formula : baezDuarteGramEntry 48 27 = vasyuninBEntry 27 48 := by
  rw [baezDuarteGramEntry_symm 48 27]
  exact G27_48_formula

theorem G48_27_interval :
    ((((134539/4610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 27) ∧
    (baezDuarteGramEntry 48 27 ≤ (((135461/4610000) : ℚ) : ℝ)) := by
  rw [G48_27_formula]
  exact vasyuninBEntry_27_48_eval

def interval_48_27 : NamedVasyuninInterval :=
{
  h := 48
  k := 27
  lower := (134539/4610000)
  upper := (135461/4610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_27_interval
}

theorem G48_28_formula : baezDuarteGramEntry 48 28 = vasyuninBEntry 28 48 := by
  rw [baezDuarteGramEntry_symm 48 28]
  exact G28_48_formula

theorem G48_28_interval :
    ((((23637571/824290000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 28) ∧
    (baezDuarteGramEntry 48 28 ≤ (((23802429/824290000) : ℚ) : ℝ)) := by
  rw [G48_28_formula]
  exact vasyuninBEntry_28_48_eval

def interval_48_28 : NamedVasyuninInterval :=
{
  h := 48
  k := 28
  lower := (23637571/824290000)
  upper := (23802429/824290000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_28_interval
}

theorem G48_29_formula : baezDuarteGramEntry 48 29 = vasyuninBEntry 29 48 := by
  rw [baezDuarteGramEntry_symm 48 29]
  exact G29_48_formula

theorem G48_29_interval :
    ((((10796799/382010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 29) ∧
    (baezDuarteGramEntry 48 29 ≤ (((10873201/382010000) : ℚ) : ℝ)) := by
  rw [G48_29_formula]
  exact vasyuninBEntry_29_48_eval

def interval_48_29 : NamedVasyuninInterval :=
{
  h := 48
  k := 29
  lower := (10796799/382010000)
  upper := (10873201/382010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_29_interval
}

theorem G48_30_formula : baezDuarteGramEntry 48 30 = vasyuninBEntry 30 48 := by
  rw [baezDuarteGramEntry_symm 48 30]
  exact G30_48_formula

theorem G48_30_interval :
    ((((417751/14990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 30) ∧
    (baezDuarteGramEntry 48 30 ≤ (((420749/14990000) : ℚ) : ℝ)) := by
  rw [G48_30_formula]
  exact vasyuninBEntry_30_48_eval

def interval_48_30 : NamedVasyuninInterval :=
{
  h := 48
  k := 30
  lower := (417751/14990000)
  upper := (420749/14990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_30_interval
}

theorem G48_31_formula : baezDuarteGramEntry 48 31 = vasyuninBEntry 31 48 := by
  rw [baezDuarteGramEntry_symm 48 31]
  exact G31_48_formula

theorem G48_31_interval :
    ((((2310613/83870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 31) ∧
    (baezDuarteGramEntry 48 31 ≤ (((2327387/83870000) : ℚ) : ℝ)) := by
  rw [G48_31_formula]
  exact vasyuninBEntry_31_48_eval

def interval_48_31 : NamedVasyuninInterval :=
{
  h := 48
  k := 31
  lower := (2310613/83870000)
  upper := (2327387/83870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_31_interval
}

theorem G48_32_formula : baezDuarteGramEntry 48 32 = vasyuninBEntry 32 48 := by
  rw [baezDuarteGramEntry_symm 48 32]
  exact G32_48_formula

theorem G48_32_interval :
    ((((3654197/133030000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 32) ∧
    (baezDuarteGramEntry 48 32 ≤ (((3680803/133030000) : ℚ) : ℝ)) := by
  rw [G48_32_formula]
  exact vasyuninBEntry_32_48_eval

def interval_48_32 : NamedVasyuninInterval :=
{
  h := 48
  k := 32
  lower := (3654197/133030000)
  upper := (3680803/133030000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_32_interval
}

theorem G48_33_formula : baezDuarteGramEntry 48 33 = vasyuninBEntry 33 48 := by
  rw [baezDuarteGramEntry_symm 48 33]
  exact G33_48_formula

theorem G48_33_interval :
    ((((21500143/798570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 33) ∧
    (baezDuarteGramEntry 48 33 ≤ (((21659857/798570000) : ℚ) : ℝ)) := by
  rw [G48_33_formula]
  exact vasyuninBEntry_33_48_eval

def interval_48_33 : NamedVasyuninInterval :=
{
  h := 48
  k := 33
  lower := (21500143/798570000)
  upper := (21659857/798570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_33_interval
}

theorem G48_34_formula : baezDuarteGramEntry 48 34 = vasyuninBEntry 34 48 := by
  rw [baezDuarteGramEntry_symm 48 34]
  exact G34_48_formula

theorem G48_34_interval :
    ((((6107033/229670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 34) ∧
    (baezDuarteGramEntry 48 34 ≤ (((6152967/229670000) : ℚ) : ℝ)) := by
  rw [G48_34_formula]
  exact vasyuninBEntry_34_48_eval

def interval_48_34 : NamedVasyuninInterval :=
{
  h := 48
  k := 34
  lower := (6107033/229670000)
  upper := (6152967/229670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_34_interval
}

theorem G48_35_formula : baezDuarteGramEntry 48 35 = vasyuninBEntry 35 48 := by
  rw [baezDuarteGramEntry_symm 48 35]
  exact G35_48_formula

theorem G48_35_interval :
    ((((16168583/614170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 35) ∧
    (baezDuarteGramEntry 48 35 ≤ (((16291417/614170000) : ℚ) : ℝ)) := by
  rw [G48_35_formula]
  exact vasyuninBEntry_35_48_eval

def interval_48_35 : NamedVasyuninInterval :=
{
  h := 48
  k := 35
  lower := (16168583/614170000)
  upper := (16291417/614170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_35_interval
}

theorem G48_36_formula : baezDuarteGramEntry 48 36 = vasyuninBEntry 36 48 := by
  rw [baezDuarteGramEntry_symm 48 36]
  exact G36_48_formula

theorem G48_36_interval :
    ((((3147979/120210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 36) ∧
    (baezDuarteGramEntry 48 36 ≤ (((3172021/120210000) : ℚ) : ℝ)) := by
  rw [G48_36_formula]
  exact vasyuninBEntry_36_48_eval

def interval_48_36 : NamedVasyuninInterval :=
{
  h := 48
  k := 36
  lower := (3147979/120210000)
  upper := (3172021/120210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_36_interval
}

theorem G48_37_formula : baezDuarteGramEntry 48 37 = vasyuninBEntry 37 48 := by
  rw [baezDuarteGramEntry_symm 48 37]
  exact G37_48_formula

theorem G48_37_interval :
    ((((16167529/624710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 37) ∧
    (baezDuarteGramEntry 48 37 ≤ (((16292471/624710000) : ℚ) : ℝ)) := by
  rw [G48_37_formula]
  exact vasyuninBEntry_37_48_eval

def interval_48_37 : NamedVasyuninInterval :=
{
  h := 48
  k := 37
  lower := (16167529/624710000)
  upper := (16292471/624710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_37_interval
}

theorem G48_38_formula : baezDuarteGramEntry 48 38 = vasyuninBEntry 38 48 := by
  rw [baezDuarteGramEntry_symm 48 38]
  exact G38_48_formula

theorem G48_38_interval :
    ((((24185881/941190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 38) ∧
    (baezDuarteGramEntry 48 38 ≤ (((24374119/941190000) : ℚ) : ℝ)) := by
  rw [G48_38_formula]
  exact vasyuninBEntry_38_48_eval

def interval_48_38 : NamedVasyuninInterval :=
{
  h := 48
  k := 38
  lower := (24185881/941190000)
  upper := (24374119/941190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_38_interval
}

theorem G48_39_formula : baezDuarteGramEntry 48 39 = vasyuninBEntry 39 48 := by
  rw [baezDuarteGramEntry_symm 48 39]
  exact G39_48_formula

theorem G48_39_interval :
    ((((1378601/53990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 39) ∧
    (baezDuarteGramEntry 48 39 ≤ (((1389399/53990000) : ℚ) : ℝ)) := by
  rw [G48_39_formula]
  exact vasyuninBEntry_39_48_eval

def interval_48_39 : NamedVasyuninInterval :=
{
  h := 48
  k := 39
  lower := (1378601/53990000)
  upper := (1389399/53990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_39_interval
}

theorem G48_40_formula : baezDuarteGramEntry 48 40 = vasyuninBEntry 40 48 := by
  rw [baezDuarteGramEntry_symm 48 40]
  exact G40_48_formula

theorem G48_40_interval :
    ((((4357859/171410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 40) ∧
    (baezDuarteGramEntry 48 40 ≤ (((4392141/171410000) : ℚ) : ℝ)) := by
  rw [G48_40_formula]
  exact vasyuninBEntry_40_48_eval

def interval_48_40 : NamedVasyuninInterval :=
{
  h := 48
  k := 40
  lower := (4357859/171410000)
  upper := (4392141/171410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_40_interval
}

theorem G48_41_formula : baezDuarteGramEntry 48 41 = vasyuninBEntry 41 48 := by
  rw [baezDuarteGramEntry_symm 48 41]
  exact G41_48_formula

theorem G48_41_interval :
    ((((16534651/653490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 41) ∧
    (baezDuarteGramEntry 48 41 ≤ (((16665349/653490000) : ℚ) : ℝ)) := by
  rw [G48_41_formula]
  exact vasyuninBEntry_41_48_eval

def interval_48_41 : NamedVasyuninInterval :=
{
  h := 48
  k := 41
  lower := (16534651/653490000)
  upper := (16665349/653490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_41_interval
}

theorem G48_42_formula : baezDuarteGramEntry 48 42 = vasyuninBEntry 42 48 := by
  rw [baezDuarteGramEntry_symm 48 42]
  exact G42_48_formula

theorem G48_42_interval :
    ((((9661719/382810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 42) ∧
    (baezDuarteGramEntry 48 42 ≤ (((9738281/382810000) : ℚ) : ℝ)) := by
  rw [G48_42_formula]
  exact vasyuninBEntry_42_48_eval

def interval_48_42 : NamedVasyuninInterval :=
{
  h := 48
  k := 42
  lower := (9661719/382810000)
  upper := (9738281/382810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_42_interval
}

theorem G48_43_formula : baezDuarteGramEntry 48 43 = vasyuninBEntry 43 48 := by
  rw [baezDuarteGramEntry_symm 48 43]
  exact G43_48_formula

theorem G48_43_interval :
    ((((2388521/94790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 43) ∧
    (baezDuarteGramEntry 48 43 ≤ (((2407479/94790000) : ℚ) : ℝ)) := by
  rw [G48_43_formula]
  exact vasyuninBEntry_43_48_eval

def interval_48_43 : NamedVasyuninInterval :=
{
  h := 48
  k := 43
  lower := (2388521/94790000)
  upper := (2407479/94790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_43_interval
}

theorem G48_44_formula : baezDuarteGramEntry 48 44 = vasyuninBEntry 44 48 := by
  rw [baezDuarteGramEntry_symm 48 44]
  exact G44_48_formula

theorem G48_44_interval :
    ((((7669579/304210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 44) ∧
    (baezDuarteGramEntry 48 44 ≤ (((7730421/304210000) : ℚ) : ℝ)) := by
  rw [G48_44_formula]
  exact vasyuninBEntry_44_48_eval

def interval_48_44 : NamedVasyuninInterval :=
{
  h := 48
  k := 44
  lower := (7669579/304210000)
  upper := (7730421/304210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_44_interval
}

theorem G48_45_formula : baezDuarteGramEntry 48 45 = vasyuninBEntry 45 48 := by
  rw [baezDuarteGramEntry_symm 48 45]
  exact G45_48_formula

theorem G48_45_interval :
    ((((2557879/101210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 45) ∧
    (baezDuarteGramEntry 48 45 ≤ (((2578121/101210000) : ℚ) : ℝ)) := by
  rw [G48_45_formula]
  exact vasyuninBEntry_45_48_eval

def interval_48_45 : NamedVasyuninInterval :=
{
  h := 48
  k := 45
  lower := (2557879/101210000)
  upper := (2578121/101210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_45_interval
}

theorem G48_46_formula : baezDuarteGramEntry 48 46 = vasyuninBEntry 46 48 := by
  rw [baezDuarteGramEntry_symm 48 46]
  exact G46_48_formula

theorem G48_46_interval :
    ((((10598281/417190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 46) ∧
    (baezDuarteGramEntry 48 46 ≤ (((10681719/417190000) : ℚ) : ℝ)) := by
  rw [G48_46_formula]
  exact vasyuninBEntry_46_48_eval

def interval_48_46 : NamedVasyuninInterval :=
{
  h := 48
  k := 46
  lower := (10598281/417190000)
  upper := (10681719/417190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_46_interval
}

theorem G48_47_formula : baezDuarteGramEntry 48 47 = vasyuninBEntry 47 48 := by
  rw [baezDuarteGramEntry_symm 48 47]
  exact G47_48_formula

theorem G48_47_interval :
    ((((4041737/157630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 47) ∧
    (baezDuarteGramEntry 48 47 ≤ (((4073263/157630000) : ℚ) : ℝ)) := by
  rw [G48_47_formula]
  exact vasyuninBEntry_47_48_eval

def interval_48_47 : NamedVasyuninInterval :=
{
  h := 48
  k := 47
  lower := (4041737/157630000)
  upper := (4073263/157630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_47_interval
}

theorem G48_48_formula_eq : baezDuarteGramEntry 48 48 = (1 / (48 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 48 := by norm_num
  rw [baez_duarte_diagonal_scaling 48 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G48_48_log_gamma_interval :
  ((((24755383/946170000) : ℚ) : ℝ) ≤ (1 / (48 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (48 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((24944617/946170000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 48 (by norm_num)
  constructor
  · have : ((((24755383/946170000) : ℚ) : ℝ) ≤ (1 / (48 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (48 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((24944617/946170000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G48_48_interval : ((((24755383/946170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 48) ∧ (baezDuarteGramEntry 48 48 ≤ (((24944617/946170000) : ℚ) : ℝ)) := by
  rw [G48_48_formula_eq]
  exact G48_48_log_gamma_interval

def interval_48_48 : NamedVasyuninInterval :=
{
  h := 48
  k := 48
  lower := (24755383/946170000)
  upper := (24944617/946170000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G48_48_interval
}

theorem G48_49_formula : baezDuarteGramEntry 48 49 = vasyuninBEntry 48 49 := vasyuninBEntry_correct_axiom 48 49

theorem vasyuninBEntry_48_49_eval :
    ((((11927521/474790000) : ℚ) : ℝ) ≤ vasyuninBEntry 48 49) ∧
    (vasyuninBEntry 48 49 ≤ (((12022479/474790000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4849_formula_bound
  constructor <;> linarith

theorem G48_49_interval :
    ((((11927521/474790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 49) ∧
    (baezDuarteGramEntry 48 49 ≤ (((12022479/474790000) : ℚ) : ℝ)) := by
  rw [G48_49_formula]
  exact vasyuninBEntry_48_49_eval

def interval_48_49 : NamedVasyuninInterval :=
{
  h := 48
  k := 49
  lower := (11927521/474790000)
  upper := (12022479/474790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_49_interval
}

theorem G48_50_formula : baezDuarteGramEntry 48 50 = vasyuninBEntry 48 50 := vasyuninBEntry_correct_axiom 48 50

theorem vasyuninBEntry_48_50_eval :
    ((((173741/7121250) : ℚ) : ℝ) ≤ vasyuninBEntry 48 50) ∧
    (vasyuninBEntry 48 50 ≤ (((700661/28485000) : ℚ) : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := vasyuninBEntry_24_25_eval
  have hscale := vasyuninBEntry_off_diagonal_scaling 24 25 2 (by norm_num)
  rw [hscale]
  have hlo_mul := mul_le_mul_of_nonneg_left hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hhi_mul := mul_le_mul_of_nonneg_left hhi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor <;> linarith

theorem G48_50_interval :
    ((((173741/7121250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 48 50) ∧
    (baezDuarteGramEntry 48 50 ≤ (((700661/28485000) : ℚ) : ℝ)) := by
  rw [G48_50_formula]
  exact vasyuninBEntry_48_50_eval

def interval_48_50 : NamedVasyuninInterval :=
{
  h := 48
  k := 50
  lower := (173741/7121250)
  upper := (700661/28485000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G48_50_interval
}

theorem G49_1_formula : baezDuarteGramEntry 49 1 = vasyuninBEntry 1 49 := by
  rw [baezDuarteGramEntry_symm 49 1]
  exact G1_49_formula

theorem G49_1_interval :
    ((((1974977/31480000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 1) ∧
    (baezDuarteGramEntry 49 1 ≤ (((1981273/31480000) : ℚ) : ℝ)) := by
  rw [G49_1_formula]
  exact vasyuninBEntry_1_49_eval

def interval_49_1 : NamedVasyuninInterval :=
{
  h := 49
  k := 1
  lower := (1974977/31480000)
  upper := (1981273/31480000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_1_interval
}

theorem G49_2_formula : baezDuarteGramEntry 49 2 = vasyuninBEntry 2 49 := by
  rw [baezDuarteGramEntry_symm 49 2]
  exact G2_49_formula

theorem G49_2_interval :
    ((((54961137/988630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 2) ∧
    (baezDuarteGramEntry 49 2 ≤ (((55158863/988630000) : ℚ) : ℝ)) := by
  rw [G49_2_formula]
  exact vasyuninBEntry_2_49_eval

def interval_49_2 : NamedVasyuninInterval :=
{
  h := 49
  k := 2
  lower := (54961137/988630000)
  upper := (55158863/988630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_2_interval
}

theorem G49_3_formula : baezDuarteGramEntry 49 3 = vasyuninBEntry 3 49 := by
  rw [baezDuarteGramEntry_symm 49 3]
  exact G3_49_formula

theorem G49_3_interval :
    ((((25181047/489530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 3) ∧
    (baezDuarteGramEntry 49 3 ≤ (((25278953/489530000) : ℚ) : ℝ)) := by
  rw [G49_3_formula]
  exact vasyuninBEntry_3_49_eval

def interval_49_3 : NamedVasyuninInterval :=
{
  h := 49
  k := 3
  lower := (25181047/489530000)
  upper := (25278953/489530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_3_interval
}

theorem G49_4_formula : baezDuarteGramEntry 49 4 = vasyuninBEntry 4 49 := by
  rw [baezDuarteGramEntry_symm 49 4]
  exact G4_49_formula

theorem G49_4_interval :
    ((((36714313/756870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 4) ∧
    (baezDuarteGramEntry 49 4 ≤ (((36865687/756870000) : ℚ) : ℝ)) := by
  rw [G49_4_formula]
  exact vasyuninBEntry_4_49_eval

def interval_49_4 : NamedVasyuninInterval :=
{
  h := 49
  k := 4
  lower := (36714313/756870000)
  upper := (36865687/756870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_4_interval
}

theorem G49_5_formula : baezDuarteGramEntry 49 5 = vasyuninBEntry 5 49 := by
  rw [baezDuarteGramEntry_symm 49 5]
  exact G5_49_formula

theorem G49_5_interval :
    ((((2444713/52870000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 5) ∧
    (baezDuarteGramEntry 49 5 ≤ (((2455287/52870000) : ℚ) : ℝ)) := by
  rw [G49_5_formula]
  exact vasyuninBEntry_5_49_eval

def interval_49_5 : NamedVasyuninInterval :=
{
  h := 49
  k := 5
  lower := (2444713/52870000)
  upper := (2455287/52870000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_5_interval
}

theorem G49_6_formula : baezDuarteGramEntry 49 6 = vasyuninBEntry 6 49 := by
  rw [baezDuarteGramEntry_symm 49 6]
  exact G6_49_formula

theorem G49_6_interval :
    ((((25113451/565490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 6) ∧
    (baezDuarteGramEntry 49 6 ≤ (((25226549/565490000) : ℚ) : ℝ)) := by
  rw [G49_6_formula]
  exact vasyuninBEntry_6_49_eval

def interval_49_6 : NamedVasyuninInterval :=
{
  h := 49
  k := 6
  lower := (25113451/565490000)
  upper := (25226549/565490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_6_interval
}

theorem G49_7_formula : baezDuarteGramEntry 49 7 = vasyuninBEntry 7 49 := by
  rw [baezDuarteGramEntry_symm 49 7]
  exact G7_49_formula

theorem G49_7_interval :
    ((((5894363/136370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 7) ∧
    (baezDuarteGramEntry 49 7 ≤ (((5921637/136370000) : ℚ) : ℝ)) := by
  rw [G49_7_formula]
  exact vasyuninBEntry_7_49_eval

def interval_49_7 : NamedVasyuninInterval :=
{
  h := 49
  k := 7
  lower := (5894363/136370000)
  upper := (5921637/136370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_7_interval
}

theorem G49_8_formula : baezDuarteGramEntry 49 8 = vasyuninBEntry 8 49 := by
  rw [baezDuarteGramEntry_symm 49 8]
  exact G8_49_formula

theorem G49_8_interval :
    ((((25059667/603330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 8) ∧
    (baezDuarteGramEntry 49 8 ≤ (((25180333/603330000) : ℚ) : ℝ)) := by
  rw [G49_8_formula]
  exact vasyuninBEntry_8_49_eval

def interval_49_8 : NamedVasyuninInterval :=
{
  h := 49
  k := 8
  lower := (25059667/603330000)
  upper := (25180333/603330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_8_interval
}

theorem G49_9_formula : baezDuarteGramEntry 49 9 = vasyuninBEntry 9 49 := by
  rw [baezDuarteGramEntry_symm 49 9]
  exact G9_49_formula

theorem G49_9_interval :
    ((((35272109/878910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 9) ∧
    (baezDuarteGramEntry 49 9 ≤ (((35447891/878910000) : ℚ) : ℝ)) := by
  rw [G49_9_formula]
  exact vasyuninBEntry_9_49_eval

def interval_49_9 : NamedVasyuninInterval :=
{
  h := 49
  k := 9
  lower := (35272109/878910000)
  upper := (35447891/878910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_9_interval
}

theorem G49_10_formula : baezDuarteGramEntry 49 10 = vasyuninBEntry 10 49 := by
  rw [baezDuarteGramEntry_symm 49 10]
  exact G10_49_formula

theorem G49_10_interval :
    ((((2877679/73210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 10) ∧
    (baezDuarteGramEntry 49 10 ≤ (((2892321/73210000) : ℚ) : ℝ)) := by
  rw [G49_10_formula]
  exact vasyuninBEntry_10_49_eval

def interval_49_10 : NamedVasyuninInterval :=
{
  h := 49
  k := 10
  lower := (2877679/73210000)
  upper := (2892321/73210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_10_interval
}

theorem G49_11_formula : baezDuarteGramEntry 49 11 = vasyuninBEntry 11 49 := by
  rw [baezDuarteGramEntry_symm 49 11]
  exact G11_49_formula

theorem G49_11_interval :
    ((((15274867/401330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 11) ∧
    (baezDuarteGramEntry 49 11 ≤ (((15355133/401330000) : ℚ) : ℝ)) := by
  rw [G49_11_formula]
  exact vasyuninBEntry_11_49_eval

def interval_49_11 : NamedVasyuninInterval :=
{
  h := 49
  k := 11
  lower := (15274867/401330000)
  upper := (15355133/401330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_11_interval
}

theorem G49_12_formula : baezDuarteGramEntry 49 12 = vasyuninBEntry 12 49 := by
  rw [baezDuarteGramEntry_symm 49 12]
  exact G12_49_formula

theorem G49_12_interval :
    ((((4419481/117690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 12) ∧
    (baezDuarteGramEntry 49 12 ≤ (((4443019/117690000) : ℚ) : ℝ)) := by
  rw [G49_12_formula]
  exact vasyuninBEntry_12_49_eval

def interval_49_12 : NamedVasyuninInterval :=
{
  h := 49
  k := 12
  lower := (4419481/117690000)
  upper := (4443019/117690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_12_interval
}

theorem G49_13_formula : baezDuarteGramEntry 49 13 = vasyuninBEntry 13 49 := by
  rw [baezDuarteGramEntry_symm 49 13]
  exact G13_49_formula

theorem G49_13_interval :
    ((((23784659/653410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 13) ∧
    (baezDuarteGramEntry 49 13 ≤ (((23915341/653410000) : ℚ) : ℝ)) := by
  rw [G49_13_formula]
  exact vasyuninBEntry_13_49_eval

def interval_49_13 : NamedVasyuninInterval :=
{
  h := 49
  k := 13
  lower := (23784659/653410000)
  upper := (23915341/653410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_13_interval
}

theorem G49_14_formula : baezDuarteGramEntry 49 14 = vasyuninBEntry 14 49 := by
  rw [baezDuarteGramEntry_symm 49 14]
  exact G14_49_formula

theorem G49_14_interval :
    ((((139409/3910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 14) ∧
    (baezDuarteGramEntry 49 14 ≤ (((140191/3910000) : ℚ) : ℝ)) := by
  rw [G49_14_formula]
  exact vasyuninBEntry_14_49_eval

def interval_49_14 : NamedVasyuninInterval :=
{
  h := 49
  k := 14
  lower := (139409/3910000)
  upper := (140191/3910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_14_interval
}

theorem G49_15_formula : baezDuarteGramEntry 49 15 = vasyuninBEntry 15 49 := by
  rw [baezDuarteGramEntry_symm 49 15]
  exact G15_49_formula

theorem G49_15_interval :
    ((((6194767/177330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 15) ∧
    (baezDuarteGramEntry 49 15 ≤ (((6230233/177330000) : ℚ) : ℝ)) := by
  rw [G49_15_formula]
  exact vasyuninBEntry_15_49_eval

def interval_49_15 : NamedVasyuninInterval :=
{
  h := 49
  k := 15
  lower := (6194767/177330000)
  upper := (6230233/177330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_15_interval
}

theorem G49_16_formula : baezDuarteGramEntry 49 16 = vasyuninBEntry 16 49 := by
  rw [baezDuarteGramEntry_symm 49 16]
  exact G16_49_formula

theorem G49_16_interval :
    ((((4469653/128470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 16) ∧
    (baezDuarteGramEntry 49 16 ≤ (((4495347/128470000) : ℚ) : ℝ)) := by
  rw [G49_16_formula]
  exact vasyuninBEntry_16_49_eval

def interval_49_16 : NamedVasyuninInterval :=
{
  h := 49
  k := 16
  lower := (4469653/128470000)
  upper := (4495347/128470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_16_interval
}

theorem G49_17_formula : baezDuarteGramEntry 49 17 = vasyuninBEntry 17 49 := by
  rw [baezDuarteGramEntry_symm 49 17]
  exact G17_49_formula

theorem G49_17_interval :
    ((((20748779/612210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 17) ∧
    (baezDuarteGramEntry 49 17 ≤ (((20871221/612210000) : ℚ) : ℝ)) := by
  rw [G49_17_formula]
  exact vasyuninBEntry_17_49_eval

def interval_49_17 : NamedVasyuninInterval :=
{
  h := 49
  k := 17
  lower := (20748779/612210000)
  upper := (20871221/612210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_17_interval
}

theorem G49_18_formula : baezDuarteGramEntry 49 18 = vasyuninBEntry 18 49 := by
  rw [baezDuarteGramEntry_symm 49 18]
  exact G18_49_formula

theorem G49_18_interval :
    ((((23957329/726710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 18) ∧
    (baezDuarteGramEntry 49 18 ≤ (((24102671/726710000) : ℚ) : ℝ)) := by
  rw [G49_18_formula]
  exact vasyuninBEntry_18_49_eval

def interval_49_18 : NamedVasyuninInterval :=
{
  h := 49
  k := 18
  lower := (23957329/726710000)
  upper := (24102671/726710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_18_interval
}

theorem G49_19_formula : baezDuarteGramEntry 49 19 = vasyuninBEntry 19 49 := by
  rw [baezDuarteGramEntry_symm 49 19]
  exact G19_49_formula

theorem G49_19_interval :
    ((((29658291/917090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 19) ∧
    (baezDuarteGramEntry 49 19 ≤ (((29841709/917090000) : ℚ) : ℝ)) := by
  rw [G49_19_formula]
  exact vasyuninBEntry_19_49_eval

def interval_49_19 : NamedVasyuninInterval :=
{
  h := 49
  k := 19
  lower := (29658291/917090000)
  upper := (29841709/917090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_19_interval
}

theorem G49_20_formula : baezDuarteGramEntry 49 20 = vasyuninBEntry 20 49 := by
  rw [baezDuarteGramEntry_symm 49 20]
  exact G20_49_formula

theorem G49_20_interval :
    ((((1109017/34830000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 20) ∧
    (baezDuarteGramEntry 49 20 ≤ (((1115983/34830000) : ℚ) : ℝ)) := by
  rw [G49_20_formula]
  exact vasyuninBEntry_20_49_eval

def interval_49_20 : NamedVasyuninInterval :=
{
  h := 49
  k := 20
  lower := (1109017/34830000)
  upper := (1115983/34830000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_20_interval
}

theorem G49_21_formula : baezDuarteGramEntry 49 21 = vasyuninBEntry 21 49 := by
  rw [baezDuarteGramEntry_symm 49 21]
  exact G21_49_formula

theorem G49_21_interval :
    ((((12719539/404610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 21) ∧
    (baezDuarteGramEntry 49 21 ≤ (((12800461/404610000) : ℚ) : ℝ)) := by
  rw [G49_21_formula]
  exact vasyuninBEntry_21_49_eval

def interval_49_21 : NamedVasyuninInterval :=
{
  h := 49
  k := 21
  lower := (12719539/404610000)
  upper := (12800461/404610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_21_interval
}

theorem G49_22_formula : baezDuarteGramEntry 49 22 = vasyuninBEntry 22 49 := by
  rw [baezDuarteGramEntry_symm 49 22]
  exact G22_49_formula

theorem G49_22_interval :
    ((((8004233/257670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 22) ∧
    (baezDuarteGramEntry 49 22 ≤ (((8055767/257670000) : ℚ) : ℝ)) := by
  rw [G49_22_formula]
  exact vasyuninBEntry_22_49_eval

def interval_49_22 : NamedVasyuninInterval :=
{
  h := 49
  k := 22
  lower := (8004233/257670000)
  upper := (8055767/257670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_22_interval
}

theorem G49_23_formula : baezDuarteGramEntry 49 23 = vasyuninBEntry 23 49 := by
  rw [baezDuarteGramEntry_symm 49 23]
  exact G23_49_formula

theorem G49_23_interval :
    ((((11482847/371530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 23) ∧
    (baezDuarteGramEntry 49 23 ≤ (((11557153/371530000) : ℚ) : ℝ)) := by
  rw [G49_23_formula]
  exact vasyuninBEntry_23_49_eval

def interval_49_23 : NamedVasyuninInterval :=
{
  h := 49
  k := 23
  lower := (11482847/371530000)
  upper := (11557153/371530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_23_interval
}

theorem G49_24_formula : baezDuarteGramEntry 49 24 = vasyuninBEntry 24 49 := by
  rw [baezDuarteGramEntry_symm 49 24]
  exact G24_49_formula

theorem G49_24_interval :
    ((((3671917/118330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 24) ∧
    (baezDuarteGramEntry 49 24 ≤ (((3695583/118330000) : ℚ) : ℝ)) := by
  rw [G49_24_formula]
  exact vasyuninBEntry_24_49_eval

def interval_49_24 : NamedVasyuninInterval :=
{
  h := 49
  k := 24
  lower := (3671917/118330000)
  upper := (3695583/118330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_24_interval
}

theorem G49_25_formula : baezDuarteGramEntry 49 25 = vasyuninBEntry 25 49 := by
  rw [baezDuarteGramEntry_symm 49 25]
  exact G25_49_formula

theorem G49_25_interval :
    ((((7485521/244790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 25) ∧
    (baezDuarteGramEntry 49 25 ≤ (((7534479/244790000) : ℚ) : ℝ)) := by
  rw [G49_25_formula]
  exact vasyuninBEntry_25_49_eval

def interval_49_25 : NamedVasyuninInterval :=
{
  h := 49
  k := 25
  lower := (7485521/244790000)
  upper := (7534479/244790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_25_interval
}

theorem G49_26_formula : baezDuarteGramEntry 49 26 = vasyuninBEntry 26 49 := by
  rw [baezDuarteGramEntry_symm 49 26]
  exact G26_49_formula

theorem G49_26_interval :
    ((((9786933/330670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 26) ∧
    (baezDuarteGramEntry 49 26 ≤ (((9853067/330670000) : ℚ) : ℝ)) := by
  rw [G49_26_formula]
  exact vasyuninBEntry_26_49_eval

def interval_49_26 : NamedVasyuninInterval :=
{
  h := 49
  k := 26
  lower := (9786933/330670000)
  upper := (9853067/330670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_26_interval
}

theorem G49_27_formula : baezDuarteGramEntry 49 27 = vasyuninBEntry 27 49 := by
  rw [baezDuarteGramEntry_symm 49 27]
  exact G27_49_formula

theorem G49_27_interval :
    ((((305817/10580000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 27) ∧
    (baezDuarteGramEntry 49 27 ≤ (((307933/10580000) : ℚ) : ℝ)) := by
  rw [G49_27_formula]
  exact vasyuninBEntry_27_49_eval

def interval_49_27 : NamedVasyuninInterval :=
{
  h := 49
  k := 27
  lower := (305817/10580000)
  upper := (307933/10580000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_27_interval
}

theorem G49_28_formula : baezDuarteGramEntry 49 28 = vasyuninBEntry 28 49 := by
  rw [baezDuarteGramEntry_symm 49 28]
  exact G28_49_formula

theorem G49_28_interval :
    ((((7035219/247810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 28) ∧
    (baezDuarteGramEntry 49 28 ≤ (((7084781/247810000) : ℚ) : ℝ)) := by
  rw [G49_28_formula]
  exact vasyuninBEntry_28_49_eval

def interval_49_28 : NamedVasyuninInterval :=
{
  h := 49
  k := 28
  lower := (7035219/247810000)
  upper := (7084781/247810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_28_interval
}

theorem G49_29_formula : baezDuarteGramEntry 49 29 = vasyuninBEntry 29 49 := by
  rw [baezDuarteGramEntry_symm 49 29]
  exact G29_49_formula

theorem G49_29_interval :
    ((((23535683/843170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 29) ∧
    (baezDuarteGramEntry 49 29 ≤ (((23704317/843170000) : ℚ) : ℝ)) := by
  rw [G49_29_formula]
  exact vasyuninBEntry_29_49_eval

def interval_49_29 : NamedVasyuninInterval :=
{
  h := 49
  k := 29
  lower := (23535683/843170000)
  upper := (23704317/843170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_29_interval
}

theorem G49_30_formula : baezDuarteGramEntry 49 30 = vasyuninBEntry 30 49 := by
  rw [baezDuarteGramEntry_symm 49 30]
  exact G30_49_formula

theorem G49_30_interval :
    ((((6207433/225670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 30) ∧
    (baezDuarteGramEntry 49 30 ≤ (((6252567/225670000) : ℚ) : ℝ)) := by
  rw [G49_30_formula]
  exact vasyuninBEntry_30_49_eval

def interval_49_30 : NamedVasyuninInterval :=
{
  h := 49
  k := 30
  lower := (6207433/225670000)
  upper := (6252567/225670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_30_interval
}

theorem G49_31_formula : baezDuarteGramEntry 49 31 = vasyuninBEntry 31 49 := by
  rw [baezDuarteGramEntry_symm 49 31]
  exact G31_49_formula

theorem G49_31_interval :
    ((((687967/25330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 31) ∧
    (baezDuarteGramEntry 49 31 ≤ (((693033/25330000) : ℚ) : ℝ)) := by
  rw [G49_31_formula]
  exact vasyuninBEntry_31_49_eval

def interval_49_31 : NamedVasyuninInterval :=
{
  h := 49
  k := 31
  lower := (687967/25330000)
  upper := (693033/25330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_31_interval
}

theorem G49_32_formula : baezDuarteGramEntry 49 32 = vasyuninBEntry 32 49 := by
  rw [baezDuarteGramEntry_symm 49 32]
  exact G32_49_formula

theorem G49_32_interval :
    ((((14296881/531190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 32) ∧
    (baezDuarteGramEntry 49 32 ≤ (((14403119/531190000) : ℚ) : ℝ)) := by
  rw [G49_32_formula]
  exact vasyuninBEntry_32_49_eval

def interval_49_32 : NamedVasyuninInterval :=
{
  h := 49
  k := 32
  lower := (14296881/531190000)
  upper := (14403119/531190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_32_interval
}

theorem G49_33_formula : baezDuarteGramEntry 49 33 = vasyuninBEntry 33 49 := by
  rw [baezDuarteGramEntry_symm 49 33]
  exact G33_49_formula

theorem G49_33_interval :
    ((((1718557/64430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 33) ∧
    (baezDuarteGramEntry 49 33 ≤ (((1731443/64430000) : ℚ) : ℝ)) := by
  rw [G49_33_formula]
  exact vasyuninBEntry_33_49_eval

def interval_49_33 : NamedVasyuninInterval :=
{
  h := 49
  k := 33
  lower := (1718557/64430000)
  upper := (1731443/64430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_33_interval
}

theorem G49_34_formula : baezDuarteGramEntry 49 34 = vasyuninBEntry 34 49 := by
  rw [baezDuarteGramEntry_symm 49 34]
  exact G34_49_formula

theorem G49_34_interval :
    ((((21378589/814110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 34) ∧
    (baezDuarteGramEntry 49 34 ≤ (((21541411/814110000) : ℚ) : ℝ)) := by
  rw [G49_34_formula]
  exact vasyuninBEntry_34_49_eval

def interval_49_34 : NamedVasyuninInterval :=
{
  h := 49
  k := 34
  lower := (21378589/814110000)
  upper := (21541411/814110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_34_interval
}

theorem G49_35_formula : baezDuarteGramEntry 49 35 = vasyuninBEntry 35 49 := by
  rw [baezDuarteGramEntry_symm 49 35]
  exact G35_49_formula

theorem G49_35_interval :
    ((((4664549/179510000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 35) ∧
    (baezDuarteGramEntry 49 35 ≤ (((4700451/179510000) : ℚ) : ℝ)) := by
  rw [G49_35_formula]
  exact vasyuninBEntry_35_49_eval

def interval_49_35 : NamedVasyuninInterval :=
{
  h := 49
  k := 35
  lower := (4664549/179510000)
  upper := (4700451/179510000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_35_interval
}

theorem G49_36_formula : baezDuarteGramEntry 49 36 = vasyuninBEntry 36 49 := by
  rw [baezDuarteGramEntry_symm 49 36]
  exact G36_49_formula

theorem G49_36_interval :
    ((((4024359/156410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 36) ∧
    (baezDuarteGramEntry 49 36 ≤ (((4055641/156410000) : ℚ) : ℝ)) := by
  rw [G49_36_formula]
  exact vasyuninBEntry_36_49_eval

def interval_49_36 : NamedVasyuninInterval :=
{
  h := 49
  k := 36
  lower := (4024359/156410000)
  upper := (4055641/156410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_36_interval
}

theorem G49_37_formula : baezDuarteGramEntry 49 37 = vasyuninBEntry 37 49 := by
  rw [baezDuarteGramEntry_symm 49 37]
  exact G37_49_formula

theorem G49_37_interval :
    ((((22790783/892170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 37) ∧
    (baezDuarteGramEntry 49 37 ≤ (((22969217/892170000) : ℚ) : ℝ)) := by
  rw [G49_37_formula]
  exact vasyuninBEntry_37_49_eval

def interval_49_37 : NamedVasyuninInterval :=
{
  h := 49
  k := 37
  lower := (22790783/892170000)
  upper := (22969217/892170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_37_interval
}

theorem G49_38_formula : baezDuarteGramEntry 49 38 = vasyuninBEntry 38 49 := by
  rw [baezDuarteGramEntry_symm 49 38]
  exact G38_49_formula

theorem G49_38_interval :
    ((((952237/37630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 38) ∧
    (baezDuarteGramEntry 49 38 ≤ (((959763/37630000) : ℚ) : ℝ)) := by
  rw [G49_38_formula]
  exact vasyuninBEntry_38_49_eval

def interval_49_38 : NamedVasyuninInterval :=
{
  h := 49
  k := 38
  lower := (952237/37630000)
  upper := (959763/37630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_38_interval
}

theorem G49_39_formula : baezDuarteGramEntry 49 39 = vasyuninBEntry 39 49 := by
  rw [baezDuarteGramEntry_symm 49 39]
  exact G39_49_formula

theorem G49_39_interval :
    ((((21404881/851190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 39) ∧
    (baezDuarteGramEntry 49 39 ≤ (((21575119/851190000) : ℚ) : ℝ)) := by
  rw [G49_39_formula]
  exact vasyuninBEntry_39_49_eval

def interval_49_39 : NamedVasyuninInterval :=
{
  h := 49
  k := 39
  lower := (21404881/851190000)
  upper := (21575119/851190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_39_interval
}

theorem G49_40_formula : baezDuarteGramEntry 49 40 = vasyuninBEntry 40 49 := by
  rw [baezDuarteGramEntry_symm 49 40]
  exact G40_49_formula

theorem G49_40_interval :
    ((((6254963/250370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 40) ∧
    (baezDuarteGramEntry 49 40 ≤ (((6305037/250370000) : ℚ) : ℝ)) := by
  rw [G49_40_formula]
  exact vasyuninBEntry_40_49_eval

def interval_49_40 : NamedVasyuninInterval :=
{
  h := 49
  k := 40
  lower := (6254963/250370000)
  upper := (6305037/250370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_40_interval
}

theorem G49_41_formula : baezDuarteGramEntry 49 41 = vasyuninBEntry 41 49 := by
  rw [baezDuarteGramEntry_symm 49 41]
  exact G41_49_formula

theorem G49_41_interval :
    ((((4173219/167810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 41) ∧
    (baezDuarteGramEntry 49 41 ≤ (((4206781/167810000) : ℚ) : ℝ)) := by
  rw [G49_41_formula]
  exact vasyuninBEntry_41_49_eval

def interval_49_41 : NamedVasyuninInterval :=
{
  h := 49
  k := 41
  lower := (4173219/167810000)
  upper := (4206781/167810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_41_interval
}

theorem G49_42_formula : baezDuarteGramEntry 49 42 = vasyuninBEntry 42 49 := by
  rw [baezDuarteGramEntry_symm 49 42]
  exact G42_49_formula

theorem G49_42_interval :
    ((((11633059/469410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 42) ∧
    (baezDuarteGramEntry 49 42 ≤ (((11726941/469410000) : ℚ) : ℝ)) := by
  rw [G49_42_formula]
  exact vasyuninBEntry_42_49_eval

def interval_49_42 : NamedVasyuninInterval :=
{
  h := 49
  k := 42
  lower := (11633059/469410000)
  upper := (11726941/469410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_42_interval
}

theorem G49_43_formula : baezDuarteGramEntry 49 43 = vasyuninBEntry 43 49 := by
  rw [baezDuarteGramEntry_symm 49 43]
  exact G43_49_formula

theorem G49_43_interval :
    ((((1715059/69410000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 43) ∧
    (baezDuarteGramEntry 49 43 ≤ (((1728941/69410000) : ℚ) : ℝ)) := by
  rw [G49_43_formula]
  exact vasyuninBEntry_43_49_eval

def interval_49_43 : NamedVasyuninInterval :=
{
  h := 49
  k := 43
  lower := (1715059/69410000)
  upper := (1728941/69410000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_43_interval
}

theorem G49_44_formula : baezDuarteGramEntry 49 44 = vasyuninBEntry 44 49 := by
  rw [baezDuarteGramEntry_symm 49 44]
  exact G44_49_formula

theorem G49_44_interval :
    ((((11662747/472530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 44) ∧
    (baezDuarteGramEntry 49 44 ≤ (((11757253/472530000) : ℚ) : ℝ)) := by
  rw [G49_44_formula]
  exact vasyuninBEntry_44_49_eval

def interval_49_44 : NamedVasyuninInterval :=
{
  h := 49
  k := 44
  lower := (11662747/472530000)
  upper := (11757253/472530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_44_interval
}

theorem G49_45_formula : baezDuarteGramEntry 49 45 = vasyuninBEntry 45 49 := by
  rw [baezDuarteGramEntry_symm 49 45]
  exact G45_49_formula

theorem G49_45_interval :
    ((((6558443/265570000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 45) ∧
    (baezDuarteGramEntry 49 45 ≤ (((6611557/265570000) : ℚ) : ℝ)) := by
  rw [G49_45_formula]
  exact vasyuninBEntry_45_49_eval

def interval_49_45 : NamedVasyuninInterval :=
{
  h := 49
  k := 45
  lower := (6558443/265570000)
  upper := (6611557/265570000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_45_interval
}

theorem G49_46_formula : baezDuarteGramEntry 49 46 = vasyuninBEntry 46 49 := by
  rw [baezDuarteGramEntry_symm 49 46]
  exact G46_49_formula

theorem G49_46_interval :
    ((((15606967/630330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 46) ∧
    (baezDuarteGramEntry 49 46 ≤ (((15733033/630330000) : ℚ) : ℝ)) := by
  rw [G49_46_formula]
  exact vasyuninBEntry_46_49_eval

def interval_49_46 : NamedVasyuninInterval :=
{
  h := 49
  k := 46
  lower := (15606967/630330000)
  upper := (15733033/630330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_46_interval
}

theorem G49_47_formula : baezDuarteGramEntry 49 47 = vasyuninBEntry 47 49 := by
  rw [baezDuarteGramEntry_symm 49 47]
  exact G47_49_formula

theorem G49_47_interval :
    ((((23774483/955170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 47) ∧
    (baezDuarteGramEntry 49 47 ≤ (((23965517/955170000) : ℚ) : ℝ)) := by
  rw [G49_47_formula]
  exact vasyuninBEntry_47_49_eval

def interval_49_47 : NamedVasyuninInterval :=
{
  h := 49
  k := 47
  lower := (23774483/955170000)
  upper := (23965517/955170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_47_interval
}

theorem G49_48_formula : baezDuarteGramEntry 49 48 = vasyuninBEntry 48 49 := by
  rw [baezDuarteGramEntry_symm 49 48]
  exact G48_49_formula

theorem G49_48_interval :
    ((((11927521/474790000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 48) ∧
    (baezDuarteGramEntry 49 48 ≤ (((12022479/474790000) : ℚ) : ℝ)) := by
  rw [G49_48_formula]
  exact vasyuninBEntry_48_49_eval

def interval_49_48 : NamedVasyuninInterval :=
{
  h := 49
  k := 48
  lower := (11927521/474790000)
  upper := (12022479/474790000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_48_interval
}

theorem G49_49_formula_eq : baezDuarteGramEntry 49 49 = (1 / (49 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 49 := by norm_num
  rw [baez_duarte_diagonal_scaling 49 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G49_49_log_gamma_interval :
  ((((15681/611875) : ℚ) : ℝ) ≤ (1 / (49 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (49 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((126427/4895000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 49 (by norm_num)
  constructor
  · have : ((((15681/611875) : ℚ) : ℝ) ≤ (1 / (49 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (49 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((126427/4895000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G49_49_interval : ((((15681/611875) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 49) ∧ (baezDuarteGramEntry 49 49 ≤ (((126427/4895000) : ℚ) : ℝ)) := by
  rw [G49_49_formula_eq]
  exact G49_49_log_gamma_interval

def interval_49_49 : NamedVasyuninInterval :=
{
  h := 49
  k := 49
  lower := (15681/611875)
  upper := (126427/4895000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G49_49_interval
}

theorem G49_50_formula : baezDuarteGramEntry 49 50 = vasyuninBEntry 49 50 := vasyuninBEntry_correct_axiom 49 50

theorem vasyuninBEntry_49_50_eval :
    ((((1223531/49690000) : ℚ) : ℝ) ≤ vasyuninBEntry 49 50) ∧
    (vasyuninBEntry 49 50 ≤ (((1233469/49690000) : ℚ) : ℝ)) := by
  rw [vasyuninBEntry_eq_formula]
  have h_form := vasyuninBEntry_4950_formula_bound
  constructor <;> linarith

theorem G49_50_interval :
    ((((1223531/49690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 49 50) ∧
    (baezDuarteGramEntry 49 50 ≤ (((1233469/49690000) : ℚ) : ℝ)) := by
  rw [G49_50_formula]
  exact vasyuninBEntry_49_50_eval

def interval_49_50 : NamedVasyuninInterval :=
{
  h := 49
  k := 50
  lower := (1223531/49690000)
  upper := (1233469/49690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G49_50_interval
}

theorem G50_1_formula : baezDuarteGramEntry 50 1 = vasyuninBEntry 1 50 := by
  rw [baezDuarteGramEntry_symm 50 1]
  exact G1_50_formula

theorem G50_1_interval :
    ((((8232653/133470000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 1) ∧
    (baezDuarteGramEntry 50 1 ≤ (((8259347/133470000) : ℚ) : ℝ)) := by
  rw [G50_1_formula]
  exact vasyuninBEntry_1_50_eval

def interval_50_1 : NamedVasyuninInterval :=
{
  h := 50
  k := 1
  lower := (8232653/133470000)
  upper := (8259347/133470000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_1_interval
}

theorem G50_2_formula : baezDuarteGramEntry 50 2 = vasyuninBEntry 2 50 := by
  rw [baezDuarteGramEntry_symm 50 2]
  exact G2_50_formula

theorem G50_2_interval :
    ((((2106157/38430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 2) ∧
    (baezDuarteGramEntry 50 2 ≤ (((2113843/38430000) : ℚ) : ℝ)) := by
  rw [G50_2_formula]
  exact vasyuninBEntry_2_50_eval

def interval_50_2 : NamedVasyuninInterval :=
{
  h := 50
  k := 2
  lower := (2106157/38430000)
  upper := (2113843/38430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_2_interval
}

theorem G50_3_formula : baezDuarteGramEntry 50 3 = vasyuninBEntry 3 50 := by
  rw [baezDuarteGramEntry_symm 50 3]
  exact G3_50_formula

theorem G50_3_interval :
    ((((4600909/90910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 3) ∧
    (baezDuarteGramEntry 50 3 ≤ (((4619091/90910000) : ℚ) : ℝ)) := by
  rw [G50_3_formula]
  exact vasyuninBEntry_3_50_eval

def interval_50_3 : NamedVasyuninInterval :=
{
  h := 50
  k := 3
  lower := (4600909/90910000)
  upper := (4619091/90910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_3_interval
}

theorem G50_4_formula : baezDuarteGramEntry 50 4 = vasyuninBEntry 4 50 := by
  rw [baezDuarteGramEntry_symm 50 4]
  exact G4_50_formula

theorem G50_4_interval :
    ((((21215557/444430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 4) ∧
    (baezDuarteGramEntry 50 4 ≤ (((21304443/444430000) : ℚ) : ℝ)) := by
  rw [G50_4_formula]
  exact vasyuninBEntry_4_50_eval

def interval_50_4 : NamedVasyuninInterval :=
{
  h := 50
  k := 4
  lower := (21215557/444430000)
  upper := (21304443/444430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_4_interval
}

theorem G50_5_formula : baezDuarteGramEntry 50 5 = vasyuninBEntry 5 50 := by
  rw [baezDuarteGramEntry_symm 50 5]
  exact G5_50_formula

theorem G50_5_interval :
    ((((16264493/355070000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 5) ∧
    (baezDuarteGramEntry 50 5 ≤ (((16335507/355070000) : ℚ) : ℝ)) := by
  rw [G50_5_formula]
  exact vasyuninBEntry_5_50_eval

def interval_50_5 : NamedVasyuninInterval :=
{
  h := 50
  k := 5
  lower := (16264493/355070000)
  upper := (16335507/355070000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_5_interval
}

theorem G50_6_formula : baezDuarteGramEntry 50 6 = vasyuninBEntry 6 50 := by
  rw [baezDuarteGramEntry_symm 50 6]
  exact G6_50_formula

theorem G50_6_interval :
    ((((22219099/509010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 6) ∧
    (baezDuarteGramEntry 50 6 ≤ (((22320901/509010000) : ℚ) : ℝ)) := by
  rw [G50_6_formula]
  exact vasyuninBEntry_6_50_eval

def interval_50_6 : NamedVasyuninInterval :=
{
  h := 50
  k := 6
  lower := (22219099/509010000)
  upper := (22320901/509010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_6_interval
}

theorem G50_7_formula : baezDuarteGramEntry 50 7 = vasyuninBEntry 7 50 := by
  rw [baezDuarteGramEntry_symm 50 7]
  exact G7_50_formula

theorem G50_7_interval :
    ((((8150689/193110000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 7) ∧
    (baezDuarteGramEntry 50 7 ≤ (((8189311/193110000) : ℚ) : ℝ)) := by
  rw [G50_7_formula]
  exact vasyuninBEntry_7_50_eval

def interval_50_7 : NamedVasyuninInterval :=
{
  h := 50
  k := 7
  lower := (8150689/193110000)
  upper := (8189311/193110000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_7_interval
}

theorem G50_8_formula : baezDuarteGramEntry 50 8 = vasyuninBEntry 8 50 := by
  rw [baezDuarteGramEntry_symm 50 8]
  exact G8_50_formula

theorem G50_8_interval :
    ((((5546401/135990000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 8) ∧
    (baezDuarteGramEntry 50 8 ≤ (((5573599/135990000) : ℚ) : ℝ)) := by
  rw [G50_8_formula]
  exact vasyuninBEntry_8_50_eval

def interval_50_8 : NamedVasyuninInterval :=
{
  h := 50
  k := 8
  lower := (5546401/135990000)
  upper := (5573599/135990000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_8_interval
}

theorem G50_9_formula : baezDuarteGramEntry 50 9 = vasyuninBEntry 9 50 := by
  rw [baezDuarteGramEntry_symm 50 9]
  exact G9_50_formula

theorem G50_9_interval :
    ((((10732847/271530000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 9) ∧
    (baezDuarteGramEntry 50 9 ≤ (((10787153/271530000) : ℚ) : ℝ)) := by
  rw [G50_9_formula]
  exact vasyuninBEntry_9_50_eval

def interval_50_9 : NamedVasyuninInterval :=
{
  h := 50
  k := 9
  lower := (10732847/271530000)
  upper := (10787153/271530000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_9_interval
}

theorem G50_10_formula : baezDuarteGramEntry 50 10 = vasyuninBEntry 10 50 := by
  rw [baezDuarteGramEntry_symm 50 10]
  exact G10_50_formula

theorem G50_10_interval :
    ((((35519269/907310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 10) ∧
    (baezDuarteGramEntry 50 10 ≤ (((35700731/907310000) : ℚ) : ℝ)) := by
  rw [G50_10_formula]
  exact vasyuninBEntry_10_50_eval

def interval_50_10 : NamedVasyuninInterval :=
{
  h := 50
  k := 10
  lower := (35519269/907310000)
  upper := (35700731/907310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_10_interval
}

theorem G50_11_formula : baezDuarteGramEntry 50 11 = vasyuninBEntry 11 50 := by
  rw [baezDuarteGramEntry_symm 50 11]
  exact G11_50_formula

theorem G50_11_interval :
    ((((36133637/963630000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 11) ∧
    (baezDuarteGramEntry 50 11 ≤ (((36326363/963630000) : ℚ) : ℝ)) := by
  rw [G50_11_formula]
  exact vasyuninBEntry_11_50_eval

def interval_50_11 : NamedVasyuninInterval :=
{
  h := 50
  k := 11
  lower := (36133637/963630000)
  upper := (36326363/963630000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_11_interval
}

theorem G50_12_formula : baezDuarteGramEntry 50 12 = vasyuninBEntry 12 50 := by
  rw [baezDuarteGramEntry_symm 50 12]
  exact G12_50_formula

theorem G50_12_interval :
    ((((3649087/99130000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 12) ∧
    (baezDuarteGramEntry 50 12 ≤ (((3668913/99130000) : ℚ) : ℝ)) := by
  rw [G50_12_formula]
  exact vasyuninBEntry_12_50_eval

def interval_50_12 : NamedVasyuninInterval :=
{
  h := 50
  k := 12
  lower := (3649087/99130000)
  upper := (3668913/99130000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_12_interval
}

theorem G50_13_formula : baezDuarteGramEntry 50 13 = vasyuninBEntry 13 50 := by
  rw [baezDuarteGramEntry_symm 50 13]
  exact G13_50_formula

theorem G50_13_interval :
    ((((1159279/32210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 13) ∧
    (baezDuarteGramEntry 50 13 ≤ (((1165721/32210000) : ℚ) : ℝ)) := by
  rw [G50_13_formula]
  exact vasyuninBEntry_13_50_eval

def interval_50_13 : NamedVasyuninInterval :=
{
  h := 50
  k := 13
  lower := (1159279/32210000)
  upper := (1165721/32210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_13_interval
}

theorem G50_14_formula : baezDuarteGramEntry 50 14 = vasyuninBEntry 14 50 := by
  rw [baezDuarteGramEntry_symm 50 14]
  exact G14_50_formula

theorem G50_14_interval :
    ((((2557699/73010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 14) ∧
    (baezDuarteGramEntry 50 14 ≤ (((2572301/73010000) : ℚ) : ℝ)) := by
  rw [G50_14_formula]
  exact vasyuninBEntry_14_50_eval

def interval_50_14 : NamedVasyuninInterval :=
{
  h := 50
  k := 14
  lower := (2557699/73010000)
  upper := (2572301/73010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_14_interval
}

theorem G50_15_formula : baezDuarteGramEntry 50 15 = vasyuninBEntry 15 50 := by
  rw [baezDuarteGramEntry_symm 50 15]
  exact G15_50_formula

theorem G50_15_interval :
    ((((29594009/859910000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 15) ∧
    (baezDuarteGramEntry 50 15 ≤ (((29765991/859910000) : ℚ) : ℝ)) := by
  rw [G50_15_formula]
  exact vasyuninBEntry_15_50_eval

def interval_50_15 : NamedVasyuninInterval :=
{
  h := 50
  k := 15
  lower := (29594009/859910000)
  upper := (29765991/859910000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_15_interval
}

theorem G50_16_formula : baezDuarteGramEntry 50 16 = vasyuninBEntry 16 50 := by
  rw [baezDuarteGramEntry_symm 50 16]
  exact G16_50_formula

theorem G50_16_interval :
    ((((762511/22390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 16) ∧
    (baezDuarteGramEntry 50 16 ≤ (((766989/22390000) : ℚ) : ℝ)) := by
  rw [G50_16_formula]
  exact vasyuninBEntry_16_50_eval

def interval_50_16 : NamedVasyuninInterval :=
{
  h := 50
  k := 16
  lower := (762511/22390000)
  upper := (766989/22390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_16_interval
}

theorem G50_17_formula : baezDuarteGramEntry 50 17 = vasyuninBEntry 17 50 := by
  rw [baezDuarteGramEntry_symm 50 17]
  exact G17_50_formula

theorem G50_17_interval :
    ((((6069477/180230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 17) ∧
    (baezDuarteGramEntry 50 17 ≤ (((6105523/180230000) : ℚ) : ℝ)) := by
  rw [G50_17_formula]
  exact vasyuninBEntry_17_50_eval

def interval_50_17 : NamedVasyuninInterval :=
{
  h := 50
  k := 17
  lower := (6069477/180230000)
  upper := (6105523/180230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_17_interval
}

theorem G50_18_formula : baezDuarteGramEntry 50 18 = vasyuninBEntry 18 50 := by
  rw [baezDuarteGramEntry_symm 50 18]
  exact G18_50_formula

theorem G50_18_interval :
    ((((11404999/350010000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 18) ∧
    (baezDuarteGramEntry 50 18 ≤ (((11475001/350010000) : ℚ) : ℝ)) := by
  rw [G50_18_formula]
  exact vasyuninBEntry_18_50_eval

def interval_50_18 : NamedVasyuninInterval :=
{
  h := 50
  k := 18
  lower := (11404999/350010000)
  upper := (11475001/350010000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_18_interval
}

theorem G50_19_formula : baezDuarteGramEntry 50 19 = vasyuninBEntry 19 50 := by
  rw [baezDuarteGramEntry_symm 50 19]
  exact G19_50_formula

theorem G50_19_interval :
    ((((21941223/687770000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 19) ∧
    (baezDuarteGramEntry 50 19 ≤ (((22078777/687770000) : ℚ) : ℝ)) := by
  rw [G50_19_formula]
  exact vasyuninBEntry_19_50_eval

def interval_50_19 : NamedVasyuninInterval :=
{
  h := 50
  k := 19
  lower := (21941223/687770000)
  upper := (22078777/687770000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_19_interval
}

theorem G50_20_formula : baezDuarteGramEntry 50 20 = vasyuninBEntry 20 50 := by
  rw [baezDuarteGramEntry_symm 50 20]
  exact G20_50_formula

theorem G50_20_interval :
    ((((6092683/193170000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 20) ∧
    (baezDuarteGramEntry 50 20 ≤ (((6131317/193170000) : ℚ) : ℝ)) := by
  rw [G50_20_formula]
  exact vasyuninBEntry_20_50_eval

def interval_50_20 : NamedVasyuninInterval :=
{
  h := 50
  k := 20
  lower := (6092683/193170000)
  upper := (6131317/193170000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_20_interval
}

theorem G50_21_formula : baezDuarteGramEntry 50 21 = vasyuninBEntry 21 50 := by
  rw [baezDuarteGramEntry_symm 50 21]
  exact G21_50_formula

theorem G50_21_interval :
    ((((7089569/229310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 21) ∧
    (baezDuarteGramEntry 50 21 ≤ (((7135431/229310000) : ℚ) : ℝ)) := by
  rw [G50_21_formula]
  exact vasyuninBEntry_21_50_eval

def interval_50_21 : NamedVasyuninInterval :=
{
  h := 50
  k := 21
  lower := (7089569/229310000)
  upper := (7135431/229310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_21_interval
}

theorem G50_22_formula : baezDuarteGramEntry 50 22 = vasyuninBEntry 22 50 := by
  rw [baezDuarteGramEntry_symm 50 22]
  exact G22_50_formula

theorem G50_22_interval :
    ((((180011/5890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 22) ∧
    (baezDuarteGramEntry 50 22 ≤ (((181189/5890000) : ℚ) : ℝ)) := by
  rw [G50_22_formula]
  exact vasyuninBEntry_22_50_eval

def interval_50_22 : NamedVasyuninInterval :=
{
  h := 50
  k := 22
  lower := (180011/5890000)
  upper := (181189/5890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_22_interval
}

theorem G50_23_formula : baezDuarteGramEntry 50 23 = vasyuninBEntry 23 50 := by
  rw [baezDuarteGramEntry_symm 50 23]
  exact G23_50_formula

theorem G50_23_interval :
    ((((19107011/629890000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 23) ∧
    (baezDuarteGramEntry 50 23 ≤ (((19232989/629890000) : ℚ) : ℝ)) := by
  rw [G50_23_formula]
  exact vasyuninBEntry_23_50_eval

def interval_50_23 : NamedVasyuninInterval :=
{
  h := 50
  k := 23
  lower := (19107011/629890000)
  upper := (19232989/629890000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_23_interval
}

theorem G50_24_formula : baezDuarteGramEntry 50 24 = vasyuninBEntry 24 50 := by
  rw [baezDuarteGramEntry_symm 50 24]
  exact G24_50_formula

theorem G50_24_interval :
    ((((838433/27670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 24) ∧
    (baezDuarteGramEntry 50 24 ≤ (((843967/27670000) : ℚ) : ℝ)) := by
  rw [G50_24_formula]
  exact vasyuninBEntry_24_50_eval

def interval_50_24 : NamedVasyuninInterval :=
{
  h := 50
  k := 24
  lower := (838433/27670000)
  upper := (843967/27670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_24_interval
}

theorem G50_25_formula : baezDuarteGramEntry 50 25 = vasyuninBEntry 25 50 := by
  rw [baezDuarteGramEntry_symm 50 25]
  exact G25_50_formula

theorem G50_25_interval :
    ((((12265163/398370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 25) ∧
    (baezDuarteGramEntry 50 25 ≤ (((12344837/398370000) : ℚ) : ℝ)) := by
  rw [G50_25_formula]
  exact vasyuninBEntry_25_50_eval

def interval_50_25 : NamedVasyuninInterval :=
{
  h := 50
  k := 25
  lower := (12265163/398370000)
  upper := (12344837/398370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_25_interval
}

theorem G50_26_formula : baezDuarteGramEntry 50 26 = vasyuninBEntry 26 50 := by
  rw [baezDuarteGramEntry_symm 50 26]
  exact G26_50_formula

theorem G50_26_interval :
    ((((13115467/445330000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 26) ∧
    (baezDuarteGramEntry 50 26 ≤ (((13204533/445330000) : ℚ) : ℝ)) := by
  rw [G50_26_formula]
  exact vasyuninBEntry_26_50_eval

def interval_50_26 : NamedVasyuninInterval :=
{
  h := 50
  k := 26
  lower := (13115467/445330000)
  upper := (13204533/445330000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_26_interval
}

theorem G50_27_formula : baezDuarteGramEntry 50 27 = vasyuninBEntry 27 50 := by
  rw [baezDuarteGramEntry_symm 50 27]
  exact G27_50_formula

theorem G50_27_interval :
    ((((13657361/476390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 27) ∧
    (baezDuarteGramEntry 50 27 ≤ (((13752639/476390000) : ℚ) : ℝ)) := by
  rw [G50_27_formula]
  exact vasyuninBEntry_27_50_eval

def interval_50_27 : NamedVasyuninInterval :=
{
  h := 50
  k := 27
  lower := (13657361/476390000)
  upper := (13752639/476390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_27_interval
}

theorem G50_28_formula : baezDuarteGramEntry 50 28 = vasyuninBEntry 28 50 := by
  rw [baezDuarteGramEntry_symm 50 28]
  exact G28_50_formula

theorem G50_28_interval :
    ((((4421751/157490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 28) ∧
    (baezDuarteGramEntry 50 28 ≤ (((4453249/157490000) : ℚ) : ℝ)) := by
  rw [G50_28_formula]
  exact vasyuninBEntry_28_50_eval

def interval_50_28 : NamedVasyuninInterval :=
{
  h := 50
  k := 28
  lower := (4421751/157490000)
  upper := (4453249/157490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_28_interval
}

theorem G50_29_formula : baezDuarteGramEntry 50 29 = vasyuninBEntry 29 50 := by
  rw [baezDuarteGramEntry_symm 50 29]
  exact G29_50_formula

theorem G50_29_interval :
    ((((4379129/158710000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 29) ∧
    (baezDuarteGramEntry 50 29 ≤ (((4410871/158710000) : ℚ) : ℝ)) := by
  rw [G50_29_formula]
  exact vasyuninBEntry_29_50_eval

def interval_50_29 : NamedVasyuninInterval :=
{
  h := 50
  k := 29
  lower := (4379129/158710000)
  upper := (4410871/158710000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_29_interval
}

theorem G50_30_formula : baezDuarteGramEntry 50 30 = vasyuninBEntry 30 50 := by
  rw [baezDuarteGramEntry_symm 50 30]
  exact G30_50_formula

theorem G50_30_interval :
    ((((169939/6235000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 30) ∧
    (baezDuarteGramEntry 50 30 ≤ (((85593/3117500) : ℚ) : ℝ)) := by
  rw [G50_30_formula]
  exact vasyuninBEntry_30_50_eval

def interval_50_30 : NamedVasyuninInterval :=
{
  h := 50
  k := 30
  lower := (169939/6235000)
  upper := (85593/3117500)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_30_interval
}

theorem G50_31_formula : baezDuarteGramEntry 50 31 = vasyuninBEntry 31 50 := by
  rw [baezDuarteGramEntry_symm 50 31]
  exact G31_50_formula

theorem G50_31_interval :
    ((((4762241/177590000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 31) ∧
    (baezDuarteGramEntry 50 31 ≤ (((4797759/177590000) : ℚ) : ℝ)) := by
  rw [G50_31_formula]
  exact vasyuninBEntry_31_50_eval

def interval_50_31 : NamedVasyuninInterval :=
{
  h := 50
  k := 31
  lower := (4762241/177590000)
  upper := (4797759/177590000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_31_interval
}

theorem G50_32_formula : baezDuarteGramEntry 50 32 = vasyuninBEntry 32 50 := by
  rw [baezDuarteGramEntry_symm 50 32]
  exact G32_50_formula

theorem G50_32_interval :
    ((((6089533/229670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 32) ∧
    (baezDuarteGramEntry 50 32 ≤ (((6135467/229670000) : ℚ) : ℝ)) := by
  rw [G50_32_formula]
  exact vasyuninBEntry_32_50_eval

def interval_50_32 : NamedVasyuninInterval :=
{
  h := 50
  k := 32
  lower := (6089533/229670000)
  upper := (6135467/229670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_32_interval
}

theorem G50_33_formula : baezDuarteGramEntry 50 33 = vasyuninBEntry 33 50 := by
  rw [baezDuarteGramEntry_symm 50 33]
  exact G33_50_formula

theorem G50_33_interval :
    ((((637579/24210000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 33) ∧
    (baezDuarteGramEntry 50 33 ≤ (((642421/24210000) : ℚ) : ℝ)) := by
  rw [G50_33_formula]
  exact vasyuninBEntry_33_50_eval

def interval_50_33 : NamedVasyuninInterval :=
{
  h := 50
  k := 33
  lower := (637579/24210000)
  upper := (642421/24210000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_33_interval
}

theorem G50_34_formula : baezDuarteGramEntry 50 34 = vasyuninBEntry 34 50 := by
  rw [baezDuarteGramEntry_symm 50 34]
  exact G34_50_formula

theorem G50_34_interval :
    ((((23798419/915810000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 34) ∧
    (baezDuarteGramEntry 50 34 ≤ (((23981581/915810000) : ℚ) : ℝ)) := by
  rw [G50_34_formula]
  exact vasyuninBEntry_34_50_eval

def interval_50_34 : NamedVasyuninInterval :=
{
  h := 50
  k := 34
  lower := (23798419/915810000)
  upper := (23981581/915810000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_34_interval
}

theorem G50_35_formula : baezDuarteGramEntry 50 35 = vasyuninBEntry 35 50 := by
  rw [baezDuarteGramEntry_symm 50 35]
  exact G35_50_formula

theorem G50_35_interval :
    ((((16007581/624190000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 35) ∧
    (baezDuarteGramEntry 50 35 ≤ (((16132419/624190000) : ℚ) : ℝ)) := by
  rw [G50_35_formula]
  exact vasyuninBEntry_35_50_eval

def interval_50_35 : NamedVasyuninInterval :=
{
  h := 50
  k := 35
  lower := (16007581/624190000)
  upper := (16132419/624190000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_35_interval
}

theorem G50_36_formula : baezDuarteGramEntry 50 36 = vasyuninBEntry 36 50 := by
  rw [baezDuarteGramEntry_symm 50 36]
  exact G36_50_formula

theorem G50_36_interval :
    ((((25360057/999430000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 36) ∧
    (baezDuarteGramEntry 50 36 ≤ (((25559943/999430000) : ℚ) : ℝ)) := by
  rw [G50_36_formula]
  exact vasyuninBEntry_36_50_eval

def interval_50_36 : NamedVasyuninInterval :=
{
  h := 50
  k := 36
  lower := (25360057/999430000)
  upper := (25559943/999430000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_36_interval
}

theorem G50_37_formula : baezDuarteGramEntry 50 37 = vasyuninBEntry 37 50 := by
  rw [baezDuarteGramEntry_symm 50 37]
  exact G37_50_formula

theorem G50_37_interval :
    ((((1245551/49490000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 37) ∧
    (baezDuarteGramEntry 50 37 ≤ (((1255449/49490000) : ℚ) : ℝ)) := by
  rw [G50_37_formula]
  exact vasyuninBEntry_37_50_eval

def interval_50_37 : NamedVasyuninInterval :=
{
  h := 50
  k := 37
  lower := (1245551/49490000)
  upper := (1255449/49490000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_37_interval
}

theorem G50_38_formula : baezDuarteGramEntry 50 38 = vasyuninBEntry 38 50 := by
  rw [baezDuarteGramEntry_symm 50 38]
  exact G38_50_formula

theorem G50_38_interval :
    ((((850991/34090000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 38) ∧
    (baezDuarteGramEntry 50 38 ≤ (((857809/34090000) : ℚ) : ℝ)) := by
  rw [G50_38_formula]
  exact vasyuninBEntry_38_50_eval

def interval_50_38 : NamedVasyuninInterval :=
{
  h := 50
  k := 38
  lower := (850991/34090000)
  upper := (857809/34090000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_38_interval
}

theorem G50_39_formula : baezDuarteGramEntry 50 39 = vasyuninBEntry 39 50 := by
  rw [baezDuarteGramEntry_symm 50 39]
  exact G39_50_formula

theorem G50_39_interval :
    ((((3326563/134370000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 39) ∧
    (baezDuarteGramEntry 50 39 ≤ (((3353437/134370000) : ℚ) : ℝ)) := by
  rw [G50_39_formula]
  exact vasyuninBEntry_39_50_eval

def interval_50_39 : NamedVasyuninInterval :=
{
  h := 50
  k := 39
  lower := (3326563/134370000)
  upper := (3353437/134370000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_39_interval
}

theorem G50_40_formula : baezDuarteGramEntry 50 40 = vasyuninBEntry 40 50 := by
  rw [baezDuarteGramEntry_symm 50 40]
  exact G40_50_formula

theorem G50_40_interval :
    ((((11712461/475390000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 40) ∧
    (baezDuarteGramEntry 50 40 ≤ (((11807539/475390000) : ℚ) : ℝ)) := by
  rw [G50_40_formula]
  exact vasyuninBEntry_40_50_eval

def interval_50_40 : NamedVasyuninInterval :=
{
  h := 50
  k := 40
  lower := (11712461/475390000)
  upper := (11807539/475390000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_40_interval
}

theorem G50_41_formula : baezDuarteGramEntry 50 41 = vasyuninBEntry 41 50 := by
  rw [baezDuarteGramEntry_symm 50 41]
  exact G41_50_formula

theorem G50_41_interval :
    ((((22059803/901970000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 41) ∧
    (baezDuarteGramEntry 50 41 ≤ (((22240197/901970000) : ℚ) : ℝ)) := by
  rw [G50_41_formula]
  exact vasyuninBEntry_41_50_eval

def interval_50_41 : NamedVasyuninInterval :=
{
  h := 50
  k := 41
  lower := (22059803/901970000)
  upper := (22240197/901970000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_41_interval
}

theorem G50_42_formula : baezDuarteGramEntry 50 42 = vasyuninBEntry 42 50 := by
  rw [baezDuarteGramEntry_symm 50 42]
  exact G42_50_formula

theorem G50_42_interval :
    ((((23503469/965310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 42) ∧
    (baezDuarteGramEntry 50 42 ≤ (((23696531/965310000) : ℚ) : ℝ)) := by
  rw [G50_42_formula]
  exact vasyuninBEntry_42_50_eval

def interval_50_42 : NamedVasyuninInterval :=
{
  h := 50
  k := 42
  lower := (23503469/965310000)
  upper := (23696531/965310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_42_interval
}

theorem G50_43_formula : baezDuarteGramEntry 50 43 = vasyuninBEntry 43 50 := by
  rw [baezDuarteGramEntry_symm 50 43]
  exact G43_50_formula

theorem G50_43_interval :
    ((((21869869/901310000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 43) ∧
    (baezDuarteGramEntry 50 43 ≤ (((22050131/901310000) : ℚ) : ℝ)) := by
  rw [G50_43_formula]
  exact vasyuninBEntry_43_50_eval

def interval_50_43 : NamedVasyuninInterval :=
{
  h := 50
  k := 43
  lower := (21869869/901310000)
  upper := (22050131/901310000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_43_interval
}

theorem G50_44_formula : baezDuarteGramEntry 50 44 = vasyuninBEntry 44 50 := by
  rw [baezDuarteGramEntry_symm 50 44]
  exact G44_50_formula

theorem G50_44_interval :
    ((((11875939/490610000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 44) ∧
    (baezDuarteGramEntry 50 44 ≤ (((11974061/490610000) : ℚ) : ℝ)) := by
  rw [G50_44_formula]
  exact vasyuninBEntry_44_50_eval

def interval_50_44 : NamedVasyuninInterval :=
{
  h := 50
  k := 44
  lower := (11875939/490610000)
  upper := (11974061/490610000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_44_interval
}

theorem G50_45_formula : baezDuarteGramEntry 50 45 = vasyuninBEntry 45 50 := by
  rw [baezDuarteGramEntry_symm 50 45]
  exact G45_50_formula

theorem G50_45_interval :
    ((((24060531/994690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 45) ∧
    (baezDuarteGramEntry 50 45 ≤ (((24259469/994690000) : ℚ) : ℝ)) := by
  rw [G50_45_formula]
  exact vasyuninBEntry_45_50_eval

def interval_50_45 : NamedVasyuninInterval :=
{
  h := 50
  k := 45
  lower := (24060531/994690000)
  upper := (24259469/994690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_45_interval
}

theorem G50_46_formula : baezDuarteGramEntry 50 46 = vasyuninBEntry 46 50 := by
  rw [baezDuarteGramEntry_symm 50 46]
  exact G46_50_formula

theorem G50_46_interval :
    ((((20335977/840230000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 46) ∧
    (baezDuarteGramEntry 50 46 ≤ (((20504023/840230000) : ℚ) : ℝ)) := by
  rw [G50_46_formula]
  exact vasyuninBEntry_46_50_eval

def interval_50_46 : NamedVasyuninInterval :=
{
  h := 50
  k := 46
  lower := (20335977/840230000)
  upper := (20504023/840230000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_46_interval
}

theorem G50_47_formula : baezDuarteGramEntry 50 47 = vasyuninBEntry 47 50 := by
  rw [baezDuarteGramEntry_symm 50 47]
  exact G47_50_formula

theorem G50_47_interval :
    ((((23313933/960670000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 47) ∧
    (baezDuarteGramEntry 50 47 ≤ (((23506067/960670000) : ℚ) : ℝ)) := by
  rw [G50_47_formula]
  exact vasyuninBEntry_47_50_eval

def interval_50_47 : NamedVasyuninInterval :=
{
  h := 50
  k := 47
  lower := (23313933/960670000)
  upper := (23506067/960670000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_47_interval
}

theorem G50_48_formula : baezDuarteGramEntry 50 48 = vasyuninBEntry 48 50 := by
  rw [baezDuarteGramEntry_symm 50 48]
  exact G48_50_formula

theorem G50_48_interval :
    ((((173741/7121250) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 48) ∧
    (baezDuarteGramEntry 50 48 ≤ (((700661/28485000) : ℚ) : ℝ)) := by
  rw [G50_48_formula]
  exact vasyuninBEntry_48_50_eval

def interval_50_48 : NamedVasyuninInterval :=
{
  h := 50
  k := 48
  lower := (173741/7121250)
  upper := (700661/28485000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_48_interval
}

theorem G50_49_formula : baezDuarteGramEntry 50 49 = vasyuninBEntry 49 50 := by
  rw [baezDuarteGramEntry_symm 50 49]
  exact G49_50_formula

theorem G50_49_interval :
    ((((1223531/49690000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 49) ∧
    (baezDuarteGramEntry 50 49 ≤ (((1233469/49690000) : ℚ) : ℝ)) := by
  rw [G50_49_formula]
  exact vasyuninBEntry_49_50_eval

def interval_50_49 : NamedVasyuninInterval :=
{
  h := 50
  k := 49
  lower := (1223531/49690000)
  upper := (1233469/49690000)
  formulaKind := VasyuninFormulaKind.exactFormulaFuture
  lower_le_upper := by norm_num
  interval_proof := G50_49_interval
}

theorem G50_50_formula_eq : baezDuarteGramEntry 50 50 = (1 / (50 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) := by
  have hk : 0 < 50 := by norm_num
  rw [baez_duarte_diagonal_scaling 50 hk, G11_formula_theorem]
  push_cast
  rfl

theorem G50_50_log_gamma_interval :
  ((((4563827/181730000) : ℚ) : ℝ) ≤ (1 / (50 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma)) ∧
  ((1 / (50 : ℝ)) * (Real.log (2 * Real.pi) - EulerGamma) ≤ (((4600173/181730000) : ℚ) : ℝ)) := by
  have h := diag_log_gamma_interval_from_G11 50 (by norm_num)
  constructor
  · have : ((((4563827/181730000) : ℚ) : ℝ) ≤ (1 / (50 : ℝ)) * ((6303 / 5000 : ℚ) : ℝ)) := by norm_num
    linarith [h.1]
  · have : ((1 / (50 : ℝ)) * ((12607 / 10000 : ℚ) : ℝ) ≤ (((4600173/181730000) : ℚ) : ℝ)) := by norm_num
    linarith [h.2]

theorem G50_50_interval : ((((4563827/181730000) : ℚ) : ℝ) ≤ baezDuarteGramEntry 50 50) ∧ (baezDuarteGramEntry 50 50 ≤ (((4600173/181730000) : ℚ) : ℝ)) := by
  rw [G50_50_formula_eq]
  exact G50_50_log_gamma_interval

def interval_50_50 : NamedVasyuninInterval :=
{
  h := 50
  k := 50
  lower := (4563827/181730000)
  upper := (4600173/181730000)
  formulaKind := VasyuninFormulaKind.diagonalScaling
  lower_le_upper := by norm_num
  interval_proof := G50_50_interval
}

end RH.Criteria.NymanBeurling.Generated.VasyuninIntervalsN50
